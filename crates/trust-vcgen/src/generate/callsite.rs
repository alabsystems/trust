// Callsite precondition obligations: the callee's `requires` clause rewritten
// in terms of the caller's actuals. The rebinding is capture-avoiding because a
// callee parameter name can collide with a caller local, and a naive
// substitution would silently prove the wrong proposition.

use super::*;

pub fn generate_callsite_precondition_vcs(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> Vec<VerificationCondition> {
    generate_callsite_precondition_vcs_for_each(func, &[summaries]).pop().unwrap_or_default()
}

/// [`generate_callsite_precondition_vcs`] for SEVERAL summary databases over ONE caller:
/// element `i` of the result is exactly `generate_callsite_precondition_vcs(func,
/// summaries[i])`.
///
/// Trust: 2026-10-17 (gate-rca deadline, B class). The caller's whole-body analyses —
/// the arithmetic-safe view, the path-guard map, the two-pass path-definition fixpoint,
/// the statement-version oracle, the global invariant facts and the stable own
/// preconditions — read the caller and never a summary, yet the compiler's constructor
/// reconciliation (`step_by_constructor::reconcile_bundle`) asked this producer once
/// PER constructor member, each time with a one-summary database, and so rebuilt the
/// whole root's path-definition fixpoint once per member. Measured on the candidate
/// gate's `aterm_conformance::measure::scan::scan_frames`: 99.8 % of the samples of a
/// 2.5-minute native bundle construction were under this producer, in
/// `v2_path_def_fixpoint`, and the per-function clock (checked only around the whole
/// construction) declined the bundle after it had spent the function's 120 s. This
/// entry computes those analyses once and runs only the summary-dependent half (the
/// semantic guard map, the float context and the per-call loop) per database.
///
/// The output is the same as the single-database producer's by construction: the
/// shared analyses are pure functions of `func` (each is already memoized per function
/// inside a generation scope, `fn_memo` / `havoc_memo` / `place_memo`), and the
/// per-database half is the unchanged loop.
///
/// The work runs inside a VC-generation scope with its memos live and its work meter
/// OFF (`gen_work::enter_unmetered`) when no scope is active, i.e. on exactly the
/// top-level calls that today run with memos and meter both inert (the compiler's
/// constructor reconciliation, its Assert gate's regeneration and the caller
/// precondition gate). Unmetered keeps their output what it is today; the live memos
/// stop `stored_ref_pointee_names` and the shared-cell borrow map being rebuilt at every
/// call terminator of every fixpoint step (59.8 % of the same samples). A call nested in
/// a generation scope (the main lane's `discharge`) keeps that scope, metered or not.
pub fn generate_callsite_precondition_vcs_for_each(
    func: &VerifiableFunction,
    summaries: &[&crate::modular::SummaryDatabase],
) -> Vec<Vec<VerificationCondition>> {
    if summaries.is_empty() {
        return Vec::new();
    }
    let _input_analysis = super::EntryScope::enter_analysis_if_unbound(func);
    if let Some(vc) = crate::memory_image_vc(func) {
        return summaries.iter().map(|_| vec![vc.clone()]).collect();
    }
    if let Err(error) = crate::validate_function(func) {
        let vc = malformed_trust_ir_vc(func, &error);
        return summaries.iter().map(|_| vec![vc.clone()]).collect();
    }

    // verifier-perf (whole-function gate): an over-budget recursive-datatype function
    // explodes the `StmtVersionCtx::build` oracle / guard machinery below, and its own
    // `generate_vcs` already degrades it wholesale to a single Unknown. Emit NO callsite
    // precondition VCs for it. SOUNDNESS: DROP-ONLY — the whole function is already
    // fail-closed to Unknown, so withholding its (extra) callsite obligations cannot
    // manufacture a PROVE; it can only leave the function Unknown, which it already is.
    if func_exceeds_vcgen_budget(func) {
        return summaries.iter().map(|_| Vec::new()).collect();
    }
    // `TRUST_PRECOND_DEBUG=1`: the PRODUCTION-lane twin of the attributed
    // producer's per-callsite diagnostic (this producer is the one the
    // compiler's whole-function VC pipeline drives). Diagnostic only.
    static PRECOND_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let precond_debug =
        *PRECOND_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_PRECOND_DEBUG"));
    if if precond_debug {
        let tp = super::terminator_presence_for_body(&func.body);
        !tp.has_call && !tp.has_tail_call
    } else {
        !summaries.iter().any(|s| s.owes_caller_preconditions(func))
    } {
        return summaries.iter().map(|_| Vec::new()).collect();
    }
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    // The caller's own Requires clauses become guards in this lane.  Use the
    // same sanitized view as body VC generation so mathematical-Int arithmetic
    // can never be admitted as a callsite premise.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    // The memo scopes, on the view every analysis below reads (`EntryScope`: the R1
    // harvest asks this producer per (callee, caller), outside any scope).
    let _entry_scope = super::EntryScope::enter(func);
    let guard_paths_map: std::cell::OnceCell<std::rc::Rc<PathGuardMap>> =
        std::cell::OnceCell::new();
    let path_definition_map: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let sv: std::cell::OnceCell<std::rc::Rc<StmtVersionCtx>> = std::cell::OnceCell::new();
    let global_facts: std::cell::OnceCell<std::rc::Rc<RowGlobalFacts>> =
        std::cell::OnceCell::new();
    let own_preconditions: std::cell::OnceCell<Vec<Formula>> = std::cell::OnceCell::new();
    let fn_sym: Symbol = func.name.as_str().into();
    let multi_db = summaries.len() > 1;

    summaries
        .iter()
        .map(|summaries| {
            if !precond_debug && multi_db && !summaries.owes_caller_preconditions(func) {
                return Vec::new();
            }
            let semantic_guards: std::cell::OnceCell<
                std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
            > = std::cell::OnceCell::new();
            let float_ctx: std::cell::OnceCell<FloatRangeCtx<'_>> = std::cell::OnceCell::new();

            let mut vcs = Vec::new();
            for block in &func.body.blocks {
                let (callee_name, args, span) = match &block.terminator {
                    Terminator::Call { func, args, span, .. }
                    | Terminator::TailCall { func, args, span, .. } => (func, args, span),
                    _ => continue,
                };
                let Some(summary) = summaries.get(callee_name) else {
                    // Trust (I5 L0 lane — the fail-OPEN this arm used to be): a
                    // `None` here is not always "the callee has no contract". When the
                    // L0 definitional subset REFUSED a summary because it declares
                    // preconditions, the name is absent from the DB but the call site
                    // still owes the guard — and emitting nothing reported a caller
                    // that VIOLATES that precondition as CLEAN. Mint the fail-closed
                    // row instead. Ordinary absences are unaffected: only
                    // `definitional_precondition_free_subset` ever records a name.
                    if let Some(count) = summaries.l0_withheld_precondition_count(callee_name) {
                        vcs.push(crate::modular::l0_withheld_summary_vc(
                            func,
                            callee_name,
                            span,
                            count,
                        ));
                    }
                    if precond_debug {
                        eprintln!(
                            "[PRECOND_DEBUG/prod] fn={} block={} callee={callee_name} NO-SUMMARY (keys: {:?})",
                            func.name,
                            block.id.0,
                            summaries.names().collect::<Vec<_>>()
                        );
                    }
                    continue;
                };
                if precond_debug {
                    eprintln!(
                        "[PRECOND_DEBUG/prod] fn={} block={} callee={callee_name} summary: params={:?} preconds={} body={}",
                        func.name,
                        block.id.0,
                        summary.param_names,
                        summary.preconditions.len(),
                        summary.extracted_body.is_some()
                    );
                }

                if summary.preconditions.is_empty() {
                    continue;
                }
                if summary.param_names.len() != args.len() {
                    vcs.push(VerificationCondition {
                        kind: VcKind::UnsupportedMir {
                            kind: "SummaryArityMismatch".to_string(),
                            detail: format!(
                                "callee `{callee_name}` summary has {} formal parameter(s), call has {} argument(s)",
                                summary.param_names.len(),
                                args.len()
                            ),
                        },
                        function: fn_sym,
                        location: span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                        obligation: None,
                    });
                    continue;
                }

                let replacements: std::cell::OnceCell<Vec<(String, Formula)>> =
                    std::cell::OnceCell::new();
                let block_live_path_defs: std::cell::OnceCell<Vec<Formula>> =
                    std::cell::OnceCell::new();
                let block_sem_guards: std::cell::OnceCell<Vec<Formula>> =
                    std::cell::OnceCell::new();

                for precondition in &summary.preconditions {
                    // Trust (CONSTPARAM-SIGMA-FRESHEN-1): a callee-side const-generic symbol
                    // cannot be read as the caller's same-spelled param once the family is no
                    // longer freshened below. Identity on every `P` produced today; kept
                    // IDENTICAL in the attributed twin.
                    let precondition = isolate_callee_const_param_symbols_cow(precondition);
                    if contracts::formula_uses_unmodeled_machine_arithmetic(&precondition) {
                        vcs.push(contracts::spec_unverifiable_vc(
                            func,
                            span.clone(),
                            &format!(
                                "callee `{callee_name}` requires uses unmodeled fixed-width machine arithmetic"
                            ),
                            &format!("{precondition:?}"),
                            None,
                        ));
                        continue;
                    }
                    // F5 (structural caller-precondition discharge): when EVERY conjunct
                    // is a float literal bound and the σ-mapped actual's PROVEN interval
                    // sits inside the required one, the obligation provably cannot fire
                    // — it is not minted at all (the same principle as
                    // `v2_build_float_overflow_vc` returning `None` for a provably
                    // overflow-free op). Any failure falls through to the ordinary VC
                    // emission below (fail-closed). Kept IDENTICAL in the attributed
                    // twin.
                    if precondition_interval_dominance_lazy(
                        func,
                        || float_ctx.get_or_init(|| FloatRangeCtx::new(func, Some(summaries))),
                        block.id,
                        &precondition,
                        &summary.param_names,
                        args,
                        &mut Vec::new(),
                        FLOAT_EXP_BOUND_FUEL,
                    ) {
                        if precond_debug {
                            eprintln!(
                                "[PRECOND_DEBUG/prod] fn={} block={} callee={callee_name} F5-SUPPRESSED",
                                func.name, block.id.0
                            );
                        }
                        continue;
                    }
                    if precond_debug {
                        eprintln!(
                            "[PRECOND_DEBUG/prod] fn={} block={} callee={callee_name} F5-MISS -> minting VC (precond: {precondition:?})",
                            func.name, block.id.0
                        );
                    }
                    let replacements = replacements.get_or_init(|| {
                        build_callsite_sigma_replacements(func, summary, args)
                    });
                    let substituted = substitute_summary_params_owned(
                        precondition.into_owned(),
                        replacements,
                    );
                    let mut formula = Formula::Not(Box::new(substituted));

                    // Same-block STATEMENT DEFS (`_7 = 4 * m`), conjoined exactly like
                    // the UnboundedAllocation lane does: without them a callee
                    // `requires(2m <= 4m)` at `f(2*m, 4*m)` is refuted with the mul
                    // temps FREE (`_7 = 0` while `m = 2`). Establish-versioned names
                    // are bridged to ¬P[σ]'s bare spellings by the SSA normalization
                    // at the end of this loop body.
                    formula = v2_formula_with_block_defs(func, block, formula);

                    let path_definition_map = path_definition_map
                        .get_or_init(|| super::path_definition_map_for(func));
                    let sv = sv.get_or_init(|| super::stmt_versions_for(func));
                    let guard_paths_map =
                        guard_paths_map.get_or_init(|| super::guard_map_for(func));
                    let semantic_guards = semantic_guards
                        .get_or_init(|| super::semantic_guard_map_for(func, Some(summaries)));
                    let global_facts =
                        global_facts.get_or_init(|| build_global_invariant_facts(func));
                    let own_preconditions =
                        own_preconditions.get_or_init(|| stable_caller_preconditions(func));

                    // Cross-block path definitions, live-filtered against this block's
                    // own redefs and terminator kills (the postcondition lane's
                    // discipline). Spliced flat below by the sem-guard flatten.
                    let live = block_live_path_defs.get_or_init(|| {
                        block_live_callsite_path_defs(func, block, sv, path_definition_map)
                    });
                    if !live.is_empty() {
                        // Trust: restore R1 recursion inductive-bound fact (regression from
                        // 52b31a7d2a). `formula` is already the block-def-wrapped
                        // `And([arg-defs…, ¬P[σ]])`; pushing it WHOLE nests `¬P[σ]` a level deep,
                        // and when no later sem-guard flatten runs (a guarded recursive call has
                        // path defs but no semantic guards) the nesting survives to the emitted VC
                        // — so the R1 discharge gate's direct-conjunct check fails. Splice the
                        // inner conjuncts flat instead (pure `∧` associativity, verdict-identical).
                        formula = splice_flat_prefix(live, formula);
                    }

                    if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
                        formula = v2_formula_with_path_guards(
                            func,
                            sv,
                            block.id,
                            block_guard_paths,
                            formula,
                        );
                    }

                    let sem_with_bare = block_sem_guards.get_or_init(|| {
                        block_sem_guards_with_bare_variants(func, block.id, semantic_guards)
                    });
                    if !sem_with_bare.is_empty() {
                        // Trust (R1 guarded-caller discharge): FLATTEN a path-guard `And` into
                        // this semantic-guard `And` rather than nesting it. `v2_formula_with_path_guards`
                        // returns `And([path_guard, ¬P[σ]])` on a single-path block; wrapping that in
                        // another `And([sem…, And([path_guard, ¬P[σ]])])` buries `¬P[σ]` one level
                        // deep, so the `guards` extraction (which requires `¬P[σ]` to be a DIRECT
                        // conjunct of a flat `And`) yields `[]` and the obligation is rejected by
                        // `is_admissible_caller_discharge` (CallerFormulaMismatch) — even for a
                        // genuinely-guarded call. Splicing the inner conjuncts keeps `¬P[σ]` at the
                        // top level so the guard and the semantic facts are flat siblings, exactly the
                        // flat-`And` shape the discharge gate admits. Only a flat `And` is spliced; a
                        // multi-path `Or` (or a bare `¬P[σ]`) is pushed whole — an `Or`-nested `¬P[σ]`
                        // is genuinely non-flat, so `guards` stays `[]` and the gate still (soundly)
                        // rejects it. Semantics are unchanged: `And([a, And([b, c])])` and
                        // `And([a, b, c])` are the identical conjunction.
                        formula = splice_flat_prefix(sem_with_bare, formula);
                    }

                    // Global invariant facts, spliced flat for the same reason as the
                    // semantic guards above (¬P[σ] must stay a DIRECT conjunct).
                    let row_facts = global_facts.for_row(&formula);
                    if !row_facts.is_empty() {
                        let mut conjuncts = row_facts;
                        match formula {
                            Formula::And(inner) => conjuncts.extend(inner),
                            other => conjuncts.push(other),
                        }
                        formula = Formula::And(conjuncts);
                    }

                    // The caller's own STABLE preconditions, spliced flat exactly like the
                    // global facts (¬P[σ] must stay a DIRECT conjunct; in the attributed
                    // twin these surface in `guards` for the R1 discharge gate).
                    if !own_preconditions.is_empty() {
                        formula = splice_flat_prefix(own_preconditions, formula);
                    }

                    // COMPLETE alias post-pass (see `freshen_aliasing_opaque_occurrences`): per-occurrence
                    // freshen every guard/semantic-fact opaque symbol the by-name interning collapsed, so
                    // two distinct assoc-const / unevaluated-const reads can never alias into one SMT
                    // symbol (which would fabricate an equality that spuriously discharges the VC). The σ
                    // namespace (`__trust_sigma_*`) is disjoint and left intact, and so is the caller's
                    // const-generic family: one symbol is one param of THIS caller, so the guard `n < K`
                    // and σ's `buf__slice_len := K` must stay the same term (CONSTPARAM-SIGMA-FRESHEN-1).
                    let occ = std::cell::Cell::new(0u32);
                    let formula = freshen_aliasing_opaque_occurrences_owned(formula, &occ);
                    // Collapse SSA version tokens so establish-versioned block defs
                    // (`_7#s0_1 == 4 * m`) bind ¬P[σ]'s bare `_7`. ¬P[σ] itself uses
                    // bare σ names (no `#`), so it is untouched.
                    let formula = normalize_ssa_version_tokens_owned(func, formula);

                    vcs.push(VerificationCondition {
                        kind: VcKind::Precondition { callee: callee_name.clone() },
                        function: fn_sym,
                        location: span.clone(),
                        formula,
                        contract_metadata: None,
                        obligation: None,
                    });
                }
            }
            vcs
        })
        .collect()
}

/// Trust #540 (R1 2b): the ATTRIBUTED twin of [`generate_callsite_precondition_vcs`].
/// For each emitted callsite precondition VC it ALSO returns the exact `P[σ]`
/// (`substituted`) it negated and the exact TOP-LEVEL guard conjuncts it conjoined. The
/// driver feeds these into `is_admissible_caller_discharge` as
/// (`obligation = vc.formula`, `assumption_substituted = substituted`,
/// `allowed_guards = guards`). SOUNDNESS: `substituted` is the producer's pre-image of
/// `¬P[σ]` (computed from `P` and σ, NOT peeled from the obligation), so the gate's
/// `Not(substituted)` membership check is a real cross-check; `guards` are the literal
/// path/semantic conditions vcgen emitted to reach the call. Identical assembly to the
/// non-attributed producer ⇒ the returned `vc.formula` is the one the router/kernel
/// certify. Nested-`And`/`Or` shapes yield `guards = []` and the gate rejects them.
/// Unlike the general reporting producer, attributed rows stamp `vc.function`
/// with the full `func.def_path`: R1 consumes this field as proof-row identity,
/// where a short item name is not unique across modules.
pub fn generate_callsite_precondition_vcs_attributed(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> Vec<(VerificationCondition, Formula, Vec<Formula>)> {
    let _input_analysis = super::EntryScope::enter_analysis_if_unbound(func);
    if let Some(vc) = crate::memory_image_vc(func) {
        return vec![(vc, Formula::Bool(true), Vec::new())];
    }
    if let Err(error) = crate::validate_function(func) {
        return vec![(malformed_trust_ir_vc(func, &error), Formula::Bool(true), Vec::new())];
    }

    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    // `TRUST_PRECOND_DEBUG=1`: per-callsite diagnostic for the F5/F6b
    // suppression seam (which callee summaries the producer actually sees and
    // why a precondition VC was minted instead of suppressed). Diagnostic
    // only — no verdict change.
    static PRECOND_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let precond_debug =
        *PRECOND_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_PRECOND_DEBUG"));
    if if precond_debug {
        let tp = super::terminator_presence_for_body(&func.body);
        !tp.has_call && !tp.has_tail_call
    } else {
        !summaries.owes_caller_preconditions(func)
    } {
        return Vec::new();
    }
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    // The memo scopes, on the view every analysis below reads (`EntryScope`: the R1
    // harvest asks this producer per (callee, caller), outside any scope).
    let _entry_scope = super::EntryScope::enter(func);
    let guard_paths_map: std::cell::OnceCell<std::rc::Rc<PathGuardMap>> =
        std::cell::OnceCell::new();
    let semantic_guards: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let path_definition_map: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let sv: std::cell::OnceCell<std::rc::Rc<StmtVersionCtx>> = std::cell::OnceCell::new();
    let global_facts: std::cell::OnceCell<std::rc::Rc<RowGlobalFacts>> =
        std::cell::OnceCell::new();
    let own_preconditions: std::cell::OnceCell<Vec<Formula>> = std::cell::OnceCell::new();
    let float_ctx: std::cell::OnceCell<FloatRangeCtx<'_>> = std::cell::OnceCell::new();
    let fn_sym: Symbol = func.name.as_str().into();

    let mut out = Vec::new();
    for block in &func.body.blocks {
        let (callee_name, args, span) = match &block.terminator {
            Terminator::Call { func, args, span, .. }
            | Terminator::TailCall { func, args, span, .. } => (func, args, span),
            _ => continue,
        };
        let Some(summary) = summaries.get(callee_name) else {
            // Kept IDENTICAL to the non-attributed producer's arm (see there
            // for why a `None` is not always "no contract"). The attributed
            // shape carries the same always-true `not_p`/hypotheses pair the
            // sibling `SummaryArityMismatch` refusal below uses.
            if let Some(count) = summaries.l0_withheld_precondition_count(callee_name) {
                out.push((
                    crate::modular::l0_withheld_summary_vc(func, callee_name, span, count),
                    Formula::Bool(true),
                    Vec::new(),
                ));
            }
            if precond_debug {
                eprintln!(
                    "[PRECOND_DEBUG] fn={} block={} callee={callee_name} NO-SUMMARY (keys: {:?})",
                    func.name,
                    block.id.0,
                    summaries.names().collect::<Vec<_>>()
                );
            }
            continue;
        };
        if precond_debug {
            eprintln!(
                "[PRECOND_DEBUG] fn={} block={} callee={callee_name} summary: params={:?} preconds={} body={}",
                func.name,
                block.id.0,
                summary.param_names,
                summary.preconditions.len(),
                summary.extracted_body.is_some()
            );
        }

        if summary.preconditions.is_empty() {
            continue;
        }
        if summary.param_names.len() != args.len() {
            out.push((
                VerificationCondition {
                    kind: VcKind::UnsupportedMir {
                        kind: "SummaryArityMismatch".to_string(),
                        detail: format!(
                            "callee `{callee_name}` summary has {} formal parameter(s), call has {} argument(s)",
                            summary.param_names.len(),
                            args.len()
                        ),
                    },
                    function: fn_sym,
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                Formula::Bool(true),
                Vec::new(),
            ));
            continue;
        }

        let replacements: std::cell::OnceCell<Vec<(String, Formula)>> =
            std::cell::OnceCell::new();
        let block_live_path_defs: std::cell::OnceCell<Vec<Formula>> =
            std::cell::OnceCell::new();
        let block_sem_guards: std::cell::OnceCell<Vec<Formula>> =
            std::cell::OnceCell::new();

        for precondition in &summary.preconditions {
            // Trust (CONSTPARAM-SIGMA-FRESHEN-1): IDENTICAL to the non-attributed
            // producer. `substituted` (the gate's anchor) is built from this isolated
            // `P`, so `¬P[σ]` and the certified formula agree.
            let precondition = isolate_callee_const_param_symbols_cow(precondition);
            if contracts::formula_uses_unmodeled_machine_arithmetic(&precondition) {
                out.push((
                    contracts::spec_unverifiable_vc(
                        func,
                        span.clone(),
                        &format!(
                            "callee `{callee_name}` requires uses unmodeled fixed-width machine arithmetic"
                        ),
                        &format!("{precondition:?}"),
                        None,
                    ),
                    Formula::Bool(true),
                    Vec::new(),
                ));
                continue;
            }
            // F5 structural interval-dominance skip — IDENTICAL to the
            // non-attributed producer (an unminted obligation has no
            // attribution row either).
            if precondition_interval_dominance_lazy(
                func,
                || float_ctx.get_or_init(|| FloatRangeCtx::new(func, Some(summaries))),
                block.id,
                &precondition,
                &summary.param_names,
                args,
                &mut Vec::new(),
                FLOAT_EXP_BOUND_FUEL,
            ) {
                if precond_debug {
                    eprintln!(
                        "[PRECOND_DEBUG] fn={} block={} callee={callee_name} F5-SUPPRESSED",
                        func.name, block.id.0
                    );
                }
                continue;
            }
            if precond_debug {
                eprintln!(
                    "[PRECOND_DEBUG] fn={} block={} callee={callee_name} F5-MISS -> minting VC (precond: {precondition:?})",
                    func.name, block.id.0
                );
            }
            let replacements = replacements.get_or_init(|| {
                build_callsite_sigma_replacements(func, summary, args)
            });
            // The INDEPENDENT pre-image: same fn + same σ the obligation is built from.
            let substituted =
                substitute_summary_params_owned(precondition.into_owned(), replacements);
            let mut formula = Formula::Not(Box::new(substituted.clone()));

            // Same-block STATEMENT DEFS — identical to the non-attributed
            // producer (they surface in `guards` for the R1 gate; the flatten
            // below keeps ¬P[σ] a direct conjunct).
            formula = v2_formula_with_block_defs(func, block, formula);

            let path_definition_map =
                path_definition_map.get_or_init(|| super::path_definition_map_for(func));
            let sv = sv.get_or_init(|| super::stmt_versions_for(func));
            let guard_paths_map = guard_paths_map.get_or_init(|| super::guard_map_for(func));
            let semantic_guards = semantic_guards
                .get_or_init(|| super::semantic_guard_map_for(func, Some(summaries)));
            let global_facts = global_facts
                .get_or_init(|| build_global_invariant_facts(func));
            let own_preconditions =
                own_preconditions.get_or_init(|| stable_caller_preconditions(func));

            // Cross-block path definitions, live-filtered against this block's
            // own redefs and terminator kills (the postcondition lane's
            // discipline). Spliced flat below by the sem-guard flatten.
            let live = block_live_path_defs.get_or_init(|| {
                block_live_callsite_path_defs(func, block, sv, path_definition_map)
            });
            if !live.is_empty() {
                // Trust: restore R1 recursion inductive-bound fact (regression from
                // 52b31a7d2a). `formula` is already the block-def-wrapped
                // `And([arg-defs…, ¬P[σ]])`; pushing it WHOLE nests `¬P[σ]` a level deep,
                // and when no later sem-guard flatten runs (a guarded recursive call has
                // path defs but no semantic guards) the nesting survives to the emitted VC
                // — so the R1 discharge gate's direct-conjunct check fails. Splice the
                // inner conjuncts flat instead (pure `∧` associativity, verdict-identical).
                formula = splice_flat_prefix(live, formula);
            }

            if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
                formula =
                    v2_formula_with_path_guards(func, sv, block.id, block_guard_paths, formula);
            }
            let sem_with_bare = block_sem_guards.get_or_init(|| {
                block_sem_guards_with_bare_variants(func, block.id, semantic_guards)
            });
            if !sem_with_bare.is_empty() {
                // Trust (R1 guarded-caller discharge): FLATTEN a path-guard `And` into
                // this semantic-guard `And` rather than nesting it. `v2_formula_with_path_guards`
                // returns `And([path_guard, ¬P[σ]])` on a single-path block; wrapping that in
                // another `And([sem…, And([path_guard, ¬P[σ]])])` buries `¬P[σ]` one level
                // deep, so the `guards` extraction (which requires `¬P[σ]` to be a DIRECT
                // conjunct of a flat `And`) yields `[]` and the obligation is rejected by
                // `is_admissible_caller_discharge` (CallerFormulaMismatch) — even for a
                // genuinely-guarded call. Splicing the inner conjuncts keeps `¬P[σ]` at the
                // top level so the guard and the semantic facts are flat siblings, exactly the
                // flat-`And` shape the discharge gate admits. Only a flat `And` is spliced; a
                // multi-path `Or` (or a bare `¬P[σ]`) is pushed whole — an `Or`-nested `¬P[σ]`
                // is genuinely non-flat, so `guards` stays `[]` and the gate still (soundly)
                // rejects it. Semantics are unchanged: `And([a, And([b, c])])` and
                // `And([a, b, c])` are the identical conjunction.
                formula = splice_flat_prefix(sem_with_bare, formula);
            }

            // Global invariant facts, spliced flat — identical to the
            // non-attributed producer. They surface in `guards` below as
            // legitimate vcgen-emitted context for the discharge gate.
            let row_facts = global_facts.for_row(&formula);
            if !row_facts.is_empty() {
                let mut conjuncts = row_facts;
                match formula {
                    Formula::And(inner) => conjuncts.extend(inner),
                    other => conjuncts.push(other),
                }
                formula = Formula::And(conjuncts);
            }

            // The caller's own STABLE preconditions, spliced flat — identical to
            // the non-attributed producer. They surface in `guards` below as
            // legitimate vcgen-emitted context for the discharge gate.
            if !own_preconditions.is_empty() {
                formula = splice_flat_prefix(own_preconditions, formula);
            }

            // COMPLETE alias post-pass (see `freshen_aliasing_opaque_occurrences`): freshen guard /
            // semantic-fact opaque symbols per occurrence BEFORE extracting `guards`, so the gate's
            // `allowed_guards` and the certified `vc.formula` agree and no aliased equality can
            // fabricate a discharge. `¬P[σ]` (== `not_p`, the gate's structural anchor) uses the
            // disjoint `__trust_sigma_*` namespace and is preserved exactly, so the membership
            // check below still matches. The caller's const-generic symbols are not freshened
            // either (CONSTPARAM-SIGMA-FRESHEN-1): σ renders a `[T; K]` actual's length as the
            // caller's `K`, which `not_p` carries, so freshening it used to break that match too.
            let occ = std::cell::Cell::new(0u32);
            let formula = freshen_aliasing_opaque_occurrences_owned(formula, &occ);
            // Collapse SSA version tokens — identical to the non-attributed
            // producer; runs BEFORE the guards extraction, and never renames
            // `not_p` (bare σ names carry no `#`), so the membership check
            // below still matches.
            let formula = normalize_ssa_version_tokens_owned(func, formula);

            // Top-level guard conjuncts admissible for the gate: ONLY when `¬P[σ]` is a
            // DIRECT conjunct of a flat `And` (or the bare formula). Nested `And` / `Or`
            // ⇒ [] (the gate then rejects via its `not_p` membership check).
            let is_not_p =
                |f: &Formula| matches!(f, Formula::Not(inner) if inner.as_ref() == &substituted);
            let guards: Vec<Formula> = match &formula {
                f if is_not_p(f) => Vec::new(),
                Formula::And(cs) if cs.iter().rev().any(&is_not_p) => {
                    cs.iter().filter(|c| !is_not_p(c)).cloned().collect()
                }
                _ => Vec::new(),
            };

            out.push((
                VerificationCondition {
                    kind: VcKind::Precondition { callee: callee_name.clone() },
                    function: fn_sym,
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                    obligation: None,
                },
                substituted,
                guards,
            ));
        }
    }
    if !out.is_empty() {
        let def_path_sym: Symbol = func.def_path.as_str().into();
        for (vc, _, _) in &mut out {
            vc.function = def_path_sym;
        }
    }
    out
}

pub(super) fn build_callsite_sigma_replacements(
    func: &VerifiableFunction,
    summary: &crate::modular::FunctionSummary,
    args: &[Operand],
) -> Vec<(String, Formula)> {
    let mut replacements: Vec<(String, Formula)> = summary
        .param_names
        .iter()
        .zip(args.iter())
        .map(|(formal, actual)| (formal.clone(), sigma_actual_formula(func, formal, actual)))
        .collect();
    append_length_replacements(func, summary, args, &mut replacements);
    replacements
}

pub(super) fn block_live_callsite_path_defs(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    sv: &StmtVersionCtx,
    path_definition_map: &FxHashMap<BlockId, Vec<Formula>>,
) -> Vec<Formula> {
    let Some(path_defs) = path_definition_map.get(&block.id) else {
        return Vec::new();
    };
    if path_defs.is_empty() {
        return Vec::new();
    }
    let mut live = v2_live_path_defs(func, block, path_defs);
    let kill = sv.terminator_kill(func, block);
    if !kill.is_empty() {
        live.retain(|f| kill.survives(f));
    }
    live
}

pub(super) fn block_sem_guards_with_bare_variants(
    func: &VerifiableFunction,
    block_id: BlockId,
    semantic_guards: &FxHashMap<BlockId, Vec<Formula>>,
) -> Vec<Formula> {
    let Some(sem_guards) = semantic_guards.get(&block_id) else {
        return Vec::new();
    };
    if sem_guards.is_empty() {
        return Vec::new();
    }
    let mut conjuncts = sem_guards.clone();
    // BARE-named variants for SSA call-dest facts: a
    // `version_terminator_dest_fact` guard names its subject
    // `_5#s0_t`, while ¬P[σ] renders the same SSA local bare
    // (`_5`) — conjoin the identity-renamed copy so the fact
    // actually constrains the obligation. See
    // `bare_ssa_guard_variant` for the SSA soundness argument.
    conjuncts.extend(sem_guards.iter().filter_map(|g| bare_ssa_guard_variant(func, g)));
    conjuncts
}

pub(super) fn splice_flat_prefix(prefix: &[Formula], formula: Formula) -> Formula {
    let extra_len = match &formula {
        Formula::And(inner) => inner.len(),
        _ => 1,
    };
    let mut conjuncts = Vec::with_capacity(prefix.len() + extra_len);
    conjuncts.extend_from_slice(prefix);
    match formula {
        Formula::And(inner) => conjuncts.extend(inner),
        other => conjuncts.push(other),
    }
    Formula::And(conjuncts)
}

/// Split a solver variable name into `(base, projection-suffix)` at the FIRST
/// projection token (`.` field, `*` deref, `[` index, `@` downcast), the exact
/// tokens `place_to_var_name` emits. Returns `None` for a bare name (no
/// projection) — those are handled by the whole-name substitution path — and for
/// a name that starts with a projection token (no base to substitute).
pub(super) fn split_projection_base(name: &str) -> Option<(&str, &str)> {
    let idx = name.bytes().position(|b| matches!(b, b'.' | b'*' | b'[' | b'@'))?;
    if idx == 0 {
        return None;
    }
    Some((name.get(..idx)?, name.get(idx..)?))
}

/// Rebind a field-projected callee-precondition var `<formal><suffix>` to the
/// caller namespace, given the σ replacement value for `<formal>` and the callee
/// var's `sort`. SOUND (this is the load-bearing rebind for cross-call field
/// preconditions):
///
///   * A `suffix` of only field-index / deref / constant-array-index tokens
///     (`.<i>`, `*`, `[<k>]`) carries NO
///     callee-namespace-relative token, so reattaching it to the actual place
///     names EXACTLY the same nested field/pointee — `self.0` under `self -> a`
///     becomes the caller's `a.0`, the true denotation. Reattached only when the
///     replacement is a bare place `Var` (`actual_base`); the actual place's own
///     name already carries any projection it needs, and concatenation extends it.
///   * Otherwise — the actual is a compound/opaque expression (no `var_name`), or
///     the suffix contains an index-by-VAR (`[_5]`) or downcast (`@1`) token that
///     names a CALLEE local (reattaching it would silently reference an unrelated
///     caller local) — bind to a GUARANTEED-FRESH free var in the disjoint
///     `__trust_sigma_field__` namespace. It cannot collide with any caller place
///     name, so the caller obligation stays free over it and fails closed. This is
///     the fail-closed branch: never map to the wrong place, never leave the raw
///     callee formal-projected name exposed (which a same-named caller var could
///     capture).
pub(super) fn rebind_projected_actual(
    replacement: &Formula,
    suffix: &str,
    sort: Sort,
    formal_base: &str,
) -> Formula {
    // F4: the suffix must be a WELL-FORMED render token sequence
    // (`*` | `.<digits>` | `[<digits>]`)+ — see `is_safe_projection_suffix`.
    // This supersedes the old character-set check (`.`/`*`/digits only) with
    // the same accepts on every real render plus constant-index bracket
    // segments, while runtime `[_5]` / downcast `@1` segments (callee-local
    // relative) still fall to the fresh σ var.
    if is_safe_projection_suffix(suffix)
        && let Some(actual_base) = replacement.var_name()
    {
        return Formula::var_owned(format!("{actual_base}{suffix}"), sort);
    }
    Formula::var_owned(format!("__trust_sigma_field__{formal_base}{suffix}"), sort)
}

fn formula_needs_summary_param_subst(
    formula: &Formula,
    replacements: &[(String, Formula)],
) -> bool {
    trust_types::any_formula_node(formula, &mut |node| match node {
        Formula::Forall(..) | Formula::Exists(..) => true,
        _ => node.var_name().is_some_and(|name| {
            replacements.iter().any(|(formal, _)| formal == name)
                || split_projection_base(name).is_some_and(|(base, _)| {
                    replacements.iter().any(|(formal, _)| formal == base)
                })
        }),
    })
}

pub(crate) fn substitute_summary_params(
    formula: &Formula,
    replacements: &[(String, Formula)],
) -> Formula {
    if replacements.is_empty() || !formula_needs_summary_param_subst(formula, replacements) {
        return formula.clone();
    }
    substitute_summary_params_rec(formula.clone(), replacements)
}

/// Owned counterpart of [`substitute_summary_params`] that returns `formula` untouched
/// when no substitution or capture-avoiding binder rename applies and transforms in place
/// otherwise.
pub(crate) fn substitute_summary_params_owned(
    formula: Formula,
    replacements: &[(String, Formula)],
) -> Formula {
    if replacements.is_empty() || !formula_needs_summary_param_subst(&formula, replacements) {
        return formula;
    }
    substitute_summary_params_rec(formula, replacements)
}

fn substitute_summary_params_rec(
    formula: Formula,
    replacements: &[(String, Formula)],
) -> Formula {
    if replacements.is_empty() {
        return formula;
    }
    if let Some(name) = formula.var_name() {
        // Whole-name match: a scalar formal (`lo`, `self`) → its actual value.
        if let Some((_, replacement)) = replacements.iter().find(|(formal, _)| formal == name) {
            return replacement.clone();
        }
        // Field-projected callee var `<formal>.<i>` / `<formal>*.<i>`: rebind the
        // BASE per the formal→actual map, reattaching the projection suffix, so a
        // field precondition instantiates at the actual argument's field. A
        // projected var whose base is a substituted formal is ALWAYS rebound (never
        // left as the callee name), which is what keeps a same-named caller var from
        // capturing it — see `rebind_projected_actual`.
        if let Some((base, suffix)) = split_projection_base(name)
            && let Some((_, replacement)) = replacements.iter().find(|(formal, _)| formal == base)
        {
            let sort = formula.var_sort().cloned().unwrap_or(Sort::Int);
            return rebind_projected_actual(replacement, suffix, sort, base);
        }
        return formula;
    }

    match formula {
        Formula::Forall(bindings, body) => {
            // Capture-avoiding: rename any binder that would capture a free var of
            // a replacement value before substituting (soundness, round-7).
            let scoped_replacements = replacements_without_bound_vars(replacements, &bindings);
            let (bindings, body) = capture_avoiding_rebind(bindings, *body, &scoped_replacements);
            Formula::Forall(
                bindings,
                Box::new(substitute_summary_params_rec(body, &scoped_replacements)),
            )
        }
        Formula::Exists(bindings, body) => {
            let scoped_replacements = replacements_without_bound_vars(replacements, &bindings);
            let (bindings, body) = capture_avoiding_rebind(bindings, *body, &scoped_replacements);
            Formula::Exists(
                bindings,
                Box::new(substitute_summary_params_rec(body, &scoped_replacements)),
            )
        }
        other => {
            other.map_children(&mut |child| substitute_summary_params_rec(child, replacements))
        }
    }
}

/// Collect the name of every `Var` node in `formula`. Conservative: it also
/// descends into nested binders, but over-collection only triggers extra,
/// always-sound alpha-renaming.
pub(super) fn collect_var_names(formula: &Formula, out: &mut FxHashSet<String>) {
    trust_types::visit_formula_nodes(formula, &mut |node| {
        if let Some(name) = node.var_name()
            && !out.contains(name)
        {
            out.insert(name.to_string());
        }
    });
}

/// Capture-avoiding alpha-renaming for a quantifier about to be substituted by
/// [`substitute_summary_params`].
///
/// soundness (round-7 false-PROVE): callee contracts are instantiated by
/// rebinding callee formals to caller argument expressions. If a quantifier's
/// bound variable shares a name with a FREE variable of one of those argument
/// expressions, naive substitution CAPTURES that free var under the binder,
/// silently yielding a different (typically weaker) formula — a false-PROVE of a
/// quantified precondition discharge (and a false assumption for a postcondition).
/// Rename every colliding binder to a fresh, alpha-equivalent name first.
pub(super) fn capture_avoiding_rebind(
    bindings: Vec<(Symbol, Sort)>,
    body: Formula,
    active: &[(String, Formula)],
) -> (Vec<(Symbol, Sort)>, Formula) {
    // Only replacements that actually apply in this scope can cause capture.
    let has_collision = active.iter().any(|(_, value)| {
        trust_types::any_formula_node(value, &mut |n| {
            n.var_name()
                .is_some_and(|v| bindings.iter().any(|(s, _)| s.as_str() == v))
        })
    });
    if !has_collision {
        return (bindings, body);
    }

    let mut danger: FxHashSet<String> = FxHashSet::default();
    for (_, value) in active {
        collect_var_names(value, &mut danger);
    }

    // Names to avoid when minting fresh binder names.
    let mut used: FxHashSet<String> = danger.clone();
    collect_var_names(&body, &mut used);
    for (s, _) in &bindings {
        used.insert(s.as_str().to_string());
    }

    let mut new_bindings: Vec<(Symbol, Sort)> = Vec::with_capacity(bindings.len());
    let mut renamed_body = body;
    for (sym, sort) in bindings {
        if danger.contains(sym.as_str()) {
            let mut fresh = format!("{}__cap", sym.as_str());
            let mut n: u32 = 0;
            while used.contains(&fresh) {
                n += 1;
                fresh = format!("{}__cap{n}", sym.as_str());
            }
            used.insert(fresh.clone());
            // Alpha-rename this binder's occurrences in the body. The replacement
            // value is a single fresh var (no free vars of its own to capture).
            renamed_body = substitute_summary_params_owned(
                renamed_body,
                &[(sym.as_str().to_string(), Formula::var(&fresh, sort.clone()))],
            );
            new_bindings.push((Symbol::intern(&fresh), sort));
        } else {
            new_bindings.push((sym, sort));
        }
    }
    (new_bindings, renamed_body)
}

/// Instantiate a proved callee's postconditions at a specific call site.
///
/// safe-api / soundness: a callee postcondition is a fact parameterized
/// over the callee's formals and its result symbol `_0` (the callee's return
/// local, per `spec_parse` `result -> _0`). Injecting it verbatim into the
/// caller is BOTH incomplete (the fact never reaches the caller's binding) AND
/// unsound: in the caller's namespace `_0` is the *caller's own* return local,
/// so `_0 > 0` (a fact about the callee result) becomes a false premise about
/// the caller's return — a false-PROVE, since the assumption is conjoined onto
/// every body VC. Here we rebind formals -> actual argument operands and `_0` ->
/// the caller's destination place, yielding the contract's true instantiation at
/// this call. Field-projected results are left as-is (conservatively dropped,
/// never misbound). Reused by both call-site injection paths so there is a
/// single, tested rebinding point.
/// The soundness gate for assuming a callee's postcondition at a call site (the
/// gate `build_semantic_guard_map_with_summaries` applies). Shared so
/// `modular_vcgen` reports an accurate `assumptions_injected` count.
///
/// All conditions are required for SOUNDNESS / well-formedness:
/// - `has_reusable_postcondition_evidence()` — the canonical reuse bar: a private
///   authority bound to this exact summary contract. Public proof labels and
///   evidence-id strings are deliberately ignored. The ONE production minter is
///   `FunctionSummary::with_definitional_postcondition` (I5 cross-authority call
///   modeling): a clause that RESTATES a callee body its producer itself emitted
///   from a kernel-gated plan, definitionally true of every execution — see the
///   builder's authority contract. Contract-claim clauses (`with_postcondition`,
///   any label/evidence string) still never pass this bar. This is a DIFFERENT
///   axis than `proved`: a sealed-but-unverified or open-world `dyn` summary is
///   `proved` for precondition CHECKS yet must not have its postcondition
///   ASSUMED;
/// - non-empty `postconditions` — otherwise there is nothing to inject;
/// - projection-free `dest` whose post-call token names ONE value —
///   `local_defs::dest_fact_is_version_pinnable`, so a `&mut`-reassigned or
///   twice-written dest cannot leave a stale bound. This is NOT the same question
///   the stdlib min/max facts ask, and the two were the same predicate until
///   2026-08-31, when a witness proved one predicate was answering both:
///   `is_single_static_assignment` licenses a fact keyed on the dest's BARE NAME,
///   which a PARAMETER's entry definition refutes on every path that skips the
///   call. Nothing on THIS path is keyed on the bare name — the clause is threaded
///   through `version_terminator_dest_fact`, which pins every occurrence of the
///   dest's base name to `{dest}#s{block}_t`, a spelling the entry value is never
///   read under. The name-disjointness is structural: `normalize_ssa_version_tokens`
///   would be the one pass that could merge them, and `local_versions_collapse_to_bare`
///   refuses the collapse for any local with a call-dest write, which every dest
///   admitted here has by construction. The bare-name sites keep the stricter
///   question; see `local_defs`' "One predicate cannot answer two questions";
/// - arity match — otherwise the formal→arg rebinding would be ill-formed;
/// - THE TIME AXIS: no argument of this call may render to the destination's own
///   variable name. The rebound clause is threaded through
///   `version_terminator_dest_fact`, whose blanket base-name rewrite would then
///   read the argument at the POST-call token — `ensures result > n` injected as
///   `n#s{b}_t > n#s{b}_t`, an unsatisfiable hypothesis conjoined into every
///   dominated obligation. The guarded branch of `rebind_callee_postconditions`
///   has refused this for its ANTECEDENT since slice 2; the consequent — the half
///   that rides L0, because `definitional_precondition_free_subset` admits
///   precondition-free definitional summaries and those never take the guarded
///   branch — had no equivalent check until 2026-08-31. Reaching it needs
///   `_N = f(.. copy _N ..)`, which rustc does not emit (measured: 0 of 105,703
///   `Call` terminators in the dependency-closed corpus, and 0 at
///   `-Zmir-opt-level` 1/2/3/4 for eight self-assigning shapes) — so the gate
///   costs no measured fact and closes a trap nothing else in the lane refused.
///   Stated here AND enforced identically in `rebind_callee_postconditions`, on
///   the ADMIT ≡ EMIT discipline `summary_postconditions_ride_with_their_guard`
///   already keeps: this is the reason the predicate takes `args` rather than an
///   `arg_count`.
pub(crate) fn callee_postcondition_is_injectable(
    func: &VerifiableFunction,
    dest: &Place,
    summary: &crate::modular::FunctionSummary,
    args: &[Operand],
) -> bool {
    dest.projections.is_empty()
        && summary.param_names.len() == args.len()
        && !summary.postconditions.is_empty()
        && summary.has_reusable_postcondition_evidence()
        && callee_postcondition_site_admits(func, dest, summary.param_names.len(), args)
        && summary_may_inject_postcondition(summary)
        && summary.inferred_entry_bindings().is_none_or(|binding| {
            binding.matches_summary(summary) && binding.replacements(func, args, dest).is_some()
        })
}

/// The CALL-SITE half of [`callee_postcondition_is_injectable`]: everything it
/// asks that depends on this site rather than on the summary — a projection-free
/// destination, the formal/actual arity match, a version-pinnable destination,
/// and the time axis (no actual reads the destination's name). See that
/// function's doc for why each conjunct is required.
///
/// Split out (2026-09-28) so the D5-A call-destination screen can ask, AT EACH
/// CALL SITE, whether the injector really emitted a clause there — holding only
/// the callee's arity, not its summary. A callee whose clauses the injector
/// refused at this site leaves the destination free, however its summary reads.
pub(crate) fn callee_postcondition_site_admits(
    func: &VerifiableFunction,
    dest: &Place,
    formal_count: usize,
    args: &[Operand],
) -> bool {
    dest.projections.is_empty()
        && formal_count == args.len()
        && crate::local_defs::dest_fact_is_version_pinnable(func, dest.local)
        && (args.is_empty() || !terminator_args_read_name(func, args, &place_to_var_name(func, dest)))
}

fn summary_injected_param_names(
    summary: &crate::modular::FunctionSummary,
) -> Option<std::borrow::Cow<'_, [String]>> {
    match summary.inferred_entry_bindings() {
        Some(binding) => binding
            .matches_summary(summary)
            .then(|| std::borrow::Cow::Owned(binding.names())),
        None => Some(std::borrow::Cow::Borrowed(summary.param_names.as_slice())),
    }
}

/// The call-site-INDEPENDENT half of [`callee_postcondition_is_injectable`]:
/// whether `summary` carries any postcondition the injector could ever rebind
/// into a caller. A `false` here means no call to this callee has a fact
/// injected about its destination, whatever the site.
///
/// Split out so the D5-A call-destination screen
/// ([`crate::SummaryDatabase::postcondition_injecting_names`]) asks EXACTLY the
/// question the injector asks (ADMIT ≡ EMIT). A summary merely being present in
/// the DB — measured 2026-09-24: every same-crate callee of an L1 body has an
/// entry, most with no reusable postcondition — says nothing about the
/// destination, and treating presence as "pinned" left the false refutation
/// D5-A exists to hold standing.
pub(crate) fn summary_may_inject_postcondition(summary: &crate::modular::FunctionSummary) -> bool {
    !summary.postconditions.is_empty()
        && summary.has_reusable_postcondition_evidence()
        // Trust (postcondition composition, slice 2): a PRECONDITIONED summary
        // is injectable only when its clauses can ride under their own guard —
        // `summary_postconditions_ride_with_their_guard` is the shared ADMIT/EMIT
        // predicate, and `rebind_callee_postconditions` returns EMPTY on exactly
        // the same condition. A precondition-free summary is unaffected (the
        // disjunct short-circuits), and a preconditioned summary WITHOUT the
        // guard bit keeps its pre-existing behaviour on the lanes that reach it.
        && (summary.preconditions.is_empty()
            || !summary.postconditions_guarded_by_own_preconditions()
            || summary_postconditions_ride_with_their_guard(summary))
        // At least one postcondition must be fully rebindable, else nothing is
        // injected (and `assumptions_injected` would over-count).
        && summary_injected_param_names(summary).is_some_and(|param_names| {
            summary
                .postconditions
                .iter()
                .any(|p| postcondition_clause_is_injected(p, &param_names))
        })
}

/// Only a sealed body-derived clause may name its exact typed entry channels.
/// The ordinary/authored free-variable predicate remains unchanged.
#[cfg(test)]
fn summary_postcondition_clause_is_injected(
    post: &Formula,
    summary: &crate::modular::FunctionSummary,
) -> bool {
    summary_injected_param_names(summary)
        .is_some_and(|param_names| postcondition_clause_is_injected(post, &param_names))
}

/// Whether the injector emits `post` at all: the per-CLAUSE filter
/// [`rebind_callee_postconditions`] applies, shared with
/// [`summary_may_inject_postcondition`] and [`summary_pins_result`] so the
/// three cannot drift (ADMIT ≡ EMIT).
///
/// The machine-arithmetic filter has ONE structural exemption: the exact
/// single-`Ite` modular-reduction shape, whose mathematical-Int reading IS
/// fixed-width evaluation (the Clean-origin `WrappingBinOp` summary; see
/// `formula_is_exact_modular_wrapping_definition` for the soundness argument
/// and what the recognizer does and does not guarantee). A clause with a
/// non-rebindable free variable is dropped — see [`postcondition_rebindable`].
pub(crate) fn postcondition_clause_is_injected(post: &Formula, param_names: &[String]) -> bool {
    // Trust (2026-09-28, local; folded into the one predicate on merge 2026-10-14):
    // division/remainder by a positive literal is exempt too, whose Int readings ARE
    // the fixed-width evaluation (see `formula_is_exact_modular_wrapping_definition`).
    (!contracts::formula_uses_unmodeled_machine_arithmetic(post)
        || contracts::formula_is_exact_modular_wrapping_definition(post)
        || contracts::formula_is_exact_division_by_positive_literal(post))
        && postcondition_rebindable(post, param_names)
}

/// Trust (2026-09-28): whether `summary`'s injected postcondition PINS a call's
/// destination — DETERMINES the value — rather than merely constraining it.
/// This, not [`summary_may_inject_postcondition`], is the question the D5-A
/// call-destination screen (`refutation_scope`) asks before it lets a solver
/// model over the destination stand as a counterexample.
///
/// # Why "injected" is not "pinned"
///
/// A SAT model is an EXECUTION only if every value it picks is one the program
/// can produce. For a call result that holds exactly when the injected clause
/// fixes it as a function of the actuals. Two ways it does not; the first is
/// MEASURED on `p_falsefail` (2026-09-28: `dead_else` FAILED on stage 1,
/// `dead_else_s` FAILED on stage 1 and on the pack), the second follows from the
/// injected shape:
///
/// ```text
/// pub fn smax(a: u64, b: u64) -> u64 requires b <= a ensures result <= a { .. }
/// pub fn dead_else_s(a: u64) -> u64 {
///     if a > 3 { let r = smax(a, 3); if r == a { 0 } else { 3 - r } } else { 0 }
/// }
/// ```
///
/// * A BOUND. `result <= a` leaves every value up to `a` open: ay answered
///   `a = 5, r = 4, r == a false` and reported `3 - r` overflowing. The model
///   satisfies the contract; `smax(5, 3)` returns 5 and the else arm is dead.
///   Note that the guard `3 <= a` HELD in that model — proving the guard at the
///   site would not have saved it.
/// * A GUARD. A clause injected as `pre(actuals) -> post` binds nothing in a
///   model where `pre` is false, even when `post` is `result == E`. Whether the
///   site's path entails `pre` is a solver question this negative-only screen
///   cannot ask (it runs on the query alone, before and without the call's
///   `Precondition` verdict), so a guarded summary never pins.
///
/// So a summary pins exactly when it injects (the ADMIT predicate), carries NO
/// precondition — which also excludes the pre-slice-2 unguarded preconditioned
/// shape, whose clause holds only where the unchecked `requires` did — and one
/// of the clauses the injector emits has a top-level conjunct `_0 == E` (either
/// orientation) with `E` free of `_0`: a D5-B body-inferred return, a
/// Clean-origin definitional equation, an authored `ensures result == ..` on a
/// callee without `requires`.
///
/// # The cost, and why it is the least lossy sound rule here
///
/// A refutation whose query reads a bounded or guarded callee's result is
/// WITHHELD (a held `Unknown`, fail-closed, no runtime-check tolerance) instead
/// of reported `Failed`. The build outcome is the same under strict policy; what
/// changes is that Trust no longer calls a contract-level model a bug. The
/// refute-only assert lane already refuses the SAT direction for the same reason
/// (`assert_refutation`'s "exactly one `dest == rhs`" determination rule).
pub(crate) fn summary_pins_result(summary: &crate::modular::FunctionSummary) -> bool {
    !summary.postconditions.is_empty()
        && summary.preconditions.is_empty()
        && summary.has_reusable_postcondition_evidence()
        && summary_injected_param_names(summary).is_some_and(|param_names| {
            summary.postconditions.iter().any(|p| {
                postcondition_determines_result(p)
                    && postcondition_clause_is_injected(p, &param_names)
            })
        })
}

/// Whether `post` has a top-level conjunct `_0 == E` or `E == _0` with `E` free
/// of the result symbol `_0` — i.e. whether assuming it fixes the result as a
/// function of the formals. Nested under anything but `And` (an `Or`, an `Ite`,
/// an implication) it fixes nothing unconditionally, so only the conjunctive
/// spine is searched.
pub(crate) fn postcondition_determines_result(post: &Formula) -> bool {
    fn is_result(f: &Formula) -> bool {
        match f {
            Formula::Var(name, _) => name == "_0",
            Formula::SymVar(symbol, _) => symbol.as_str() == "_0",
            _ => false,
        }
    }
    fn mentions_result(f: &Formula) -> bool {
        trust_types::any_free_variable_name(f, &mut |v| v == "_0")
    }
    match post {
        Formula::And(conjuncts) => conjuncts.iter().any(postcondition_determines_result),
        Formula::Eq(lhs, rhs) => {
            (is_result(lhs) && !mentions_result(rhs)) || (is_result(rhs) && !mentions_result(lhs))
        }
        _ => false,
    }
}

/// True iff every FREE variable of `post` can be rebound at a call site — it is
/// either the callee result symbol `_0` or one of the callee's formal parameters.
///
/// SOUNDNESS (false-PROVE guard): a postcondition with any OTHER free var is
/// referencing a callee-internal symbol (e.g. `old(x)`→`old_x`, `.len()`→
/// `<base>_len`, a field / `Option`-payload derivation). Left unrebound by
/// [`rebind_callee_postconditions`] it would pass through `substitute_summary_params`
/// unchanged into the CALLER's SMT namespace, where `version_rename_at` binds it to
/// a same-named caller local the callee never constrained — a spurious conjoined
/// hypothesis that can make the violation formula UNSAT (a false-PROVE). Such a
/// clause is DROPPED (sound: dropping a hypothesis only weakens a PROVE to a FAIL).
///
/// Uses the BINDER-AWARE [`Formula::free_variables`] (not `collect_var_names`):
/// a fully-rebindable QUANTIFIED postcondition such as `forall i. _0 > i` (free
/// vars = `{_0}`) must be ACCEPTED, not dropped for its bound `i` (audit R2 #2/#4).
/// `free_variables` covers every symbol channel (`Var`, `SymVar`) and excludes
/// quantifier-bound names, so the guard stays sound while no longer over-rejecting.
pub(super) fn postcondition_rebindable(post: &Formula, param_names: &[String]) -> bool {
    trust_types::all_free_variable_names(post, &mut |v| {
        v == "_0" || param_names.iter().any(|p| p == v)
    })
}

/// True iff every FREE variable of `pre` is one of the callee's FORMALS.
///
/// The sibling of [`postcondition_rebindable`] for the precondition ANTECEDENT,
/// and deliberately STRICTER by one symbol: `_0` is excluded. A precondition is
/// a statement about the callee's ENTRY state; rebinding `_0` would bind it to
/// the caller's destination — the value the call has just PRODUCED — turning the
/// guard into a condition on the result. That antecedent could then be
/// discharged by facts about the post-state and release the postcondition on a
/// call that was never in contract.
pub(super) fn precondition_rebindable(pre: &Formula, param_names: &[String]) -> bool {
    trust_types::all_free_variable_names(pre, &mut |v| param_names.iter().any(|p| p == v))
}

/// Trust (postcondition composition, slice 2): whether `summary`'s
/// postconditions may be assumed at a call site UNDER THEIR OWN PRECONDITIONS —
/// i.e. whether the guard this summary's clauses are conditional on can actually
/// be BUILT at a call site.
///
/// This is the single predicate the ADMIT and EMIT sides share:
///   * ADMIT — [`crate::modular::SummaryDatabase::definitional_precondition_free_subset`]
///     lets a preconditioned summary into the L0 database only when this holds,
///     and [`callee_postcondition_is_injectable`] gates on it too;
///   * EMIT — [`rebind_callee_postconditions`] produces the guarded implication
///     when this holds and produces NOTHING when it does not.
///
/// They are one function rather than two spellings on purpose. The failure mode
/// of a divergence is not a missing fact, it is an UNGUARDED preconditioned
/// clause reaching a caller — the exact false PROVE this lane exists to avoid.
///
/// # Why each conjunct
///
///  * **The authority bit.** `postconditions_guarded_by_own_preconditions` is
///    the producer's assertion that `preconditions` is the callee's COMPLETE
///    authored `requires` set and that what it proved was the implication. A
///    preconditioned DEFINITIONAL summary does not carry it and keeps its
///    pre-existing withheld treatment exactly.
///  * **Every precondition must be expressible, ALL OR NOTHING.** Dropping one
///    conjunct of the antecedent yields `pre1 -> post` where the callee only
///    proved `pre1 AND pre2 -> post`. That is a STRONGER claim than the contract
///    supports, not a weaker one, so a partial guard is unsound in the ordinary
///    "dropping a hypothesis is safe" direction's OPPOSITE. Hence `all`, and
///    hence a single refusal kills the whole injection rather than the clause.
///  * **No unmodeled machine arithmetic in the guard.** The antecedent is read
///    over mathematical `Int`. If that reading is satisfiable where the callee's
///    fixed-width `requires` is false, the implication would fire outside the
///    contract. Same filter the postcondition side applies, in the direction
///    that matters for an antecedent.
///
/// A callee with NO preconditions is not this lane's business and answers
/// `false` here — its clause needs no guard and rides the ordinary path.
pub(crate) fn summary_postconditions_ride_with_their_guard(
    summary: &crate::modular::FunctionSummary,
) -> bool {
    !summary.preconditions.is_empty()
        && summary.postconditions_guarded_by_own_preconditions()
        && summary.preconditions.iter().all(|pre| {
            !contracts::formula_uses_unmodeled_machine_arithmetic(pre)
                && precondition_rebindable(pre, &summary.param_names)
        })
}

pub(crate) fn rebind_callee_postconditions(
    func: &VerifiableFunction,
    args: &[Operand],
    dest: &Place,
    summary: &crate::modular::FunctionSummary,
) -> Vec<Formula> {
    if summary.postconditions.is_empty() {
        return Vec::new();
    }
    let Some(injected_param_names) = summary_injected_param_names(summary) else {
        return Vec::new();
    };
    let injected_posts: Vec<&Formula> = summary
        .postconditions
        .iter()
        .filter(|post| postcondition_clause_is_injected(post, &injected_param_names))
        .collect();
    if injected_posts.is_empty() {
        return Vec::new();
    }
    let needs_guard =
        !summary.preconditions.is_empty() && summary.postconditions_guarded_by_own_preconditions();
    if needs_guard
        && (!summary_postconditions_ride_with_their_guard(summary)
            || summary.param_names.len() != args.len())
    {
        return Vec::new();
    }
    let ordinary_replacements = || {
        let mut out = Vec::with_capacity(summary.param_names.len().min(args.len()) + 1);
        for (formal, actual) in summary.param_names.iter().zip(args.iter()) {
            out.push((formal.clone(), operand_to_formula(func, actual)));
        }
        out
    };
    let mut replacements = match summary.inferred_entry_bindings() {
        Some(binding) => {
            if !binding.matches_summary(summary) {
                return Vec::new();
            }
            let Some(replacements) = binding.replacements(func, args, dest) else {
                return Vec::new();
            };
            replacements
        }
        None => ordinary_replacements(),
    };
    // Map the callee return symbol `_0` to the caller's destination place.
    let dest_name = place_to_var_name(func, dest);
    let dest_sort = crate::place_sort(func, dest).unwrap_or(Sort::Int);

    // THE TIME AXIS, EMIT side — the mirror of the conjunct
    // `callee_postcondition_is_injectable` applies, refusing on exactly the same
    // condition so ADMIT and EMIT cannot drift (and so `assumptions_injected`
    // never counts an injection the body VCs did not receive). If any ACTUAL
    // renders to the destination's own name, then after the `_0 -> dest`
    // substitution the clause names ONE symbol where the callee proved a relation
    // between TWO — `result > n` collapses to `n > n` before it is even versioned
    // — and `version_terminator_dest_fact` then reads the argument at the
    // post-call token. Refuse the whole injection, all-or-nothing, exactly as the
    // antecedent check below does.
    if replacements
        .iter()
        .any(|(_, actual)| trust_types::any_free_variable_name(actual, &mut |v| v == dest_name))
    {
        return Vec::new();
    }

    // Trust (postcondition composition, slice 2): THE GUARD.
    //
    // What a preconditioned callee proved is `requires -> ensures`, so that is
    // what is assumed here — the instantiated antecedent conjoined into the
    // clause, not stripped off it. The caller obtains the postcondition exactly
    // where its own path context entails the antecedent at THIS call site, and
    // obtains nothing where it does not; there is no reliance on the separately
    // emitted `VcKind::Precondition` row, which is `L1Functional` and does not
    // survive an `L0Safety` level filter.
    //
    // Built from `replacements` BEFORE `_0` joins them, so the callee result
    // symbol can never be substituted into a guard: an antecedent that could
    // mention the value the call PRODUCED would be a condition on the
    // post-state masquerading as an entry condition (`precondition_rebindable`
    // rejects `_0` outright; this ordering means even a future widening there
    // cannot bind it by accident).
    //
    // EMIT refuses on exactly the ADMIT predicate — an all-or-nothing
    // `Vec::new()`, never a partially-guarded clause. A summary with no
    // preconditions, or a preconditioned one without the guard bit, is
    // untouched and rides the pre-existing path.
    let mut guard: Option<Formula> = if !needs_guard {
        None
    } else {
        let antecedent = if let [pre] = summary.preconditions.as_slice() {
            substitute_summary_params(pre, &replacements)
        } else {
            let conjuncts: Vec<Formula> = summary
                .preconditions
                .iter()
                .map(|pre| substitute_summary_params(pre, &replacements))
                .collect();
            Formula::And(conjuncts)
        };
        // The whole implication is about to be handed to
        // `version_terminator_dest_fact`, which forces EVERY occurrence of the
        // dest's base name to the POST-call token `s{b}_t`. In the consequent
        // that is exactly right — it is what pins the fact to the value this
        // call defined. In the ANTECEDENT it would be a silent time shift: an
        // entry condition re-read against the post-state, dischargeable by
        // facts the call itself established. Refuse instead.
        //
        // SUBSUMED since 2026-08-31 by the actual-read refusal at the top of
        // this function: `precondition_rebindable` (checked above, inside
        // `summary_postconditions_ride_with_their_guard`) already confines the
        // antecedent's free variables to the formals, so after substitution its
        // symbols come only from the actuals — and an actual naming the dest is
        // now refused before we get here. Kept as belt-and-braces, on the same
        // discipline as every other superseded deny-list in this tree: it is the
        // check that NAMED the hazard, and the one a future widening of
        // `precondition_rebindable` would need.
        if trust_types::any_free_variable_name(&antecedent, &mut |v| v == dest_name) {
            return Vec::new();
        }
        Some(antecedent)
    };

    replacements.push(("_0".to_string(), Formula::var_owned(dest_name, dest_sort)));

    let last_idx = injected_posts.len() - 1;
    // A proof produced for mathematical-Int arithmetic is not authority for
    // a fixed-width Rust postcondition at the call site (exemption: the exact
    // modular-reduction shape), and a clause with a non-rebindable free var
    // is dropped BEFORE substitution — without that a stray callee symbol
    // captures a same-named caller local and can false-PROVE. ONE predicate,
    // shared with the ADMIT side (`summary_may_inject_postcondition`) and the
    // D5-A pin test (`summary_pins_result`), so the three cannot drift.
    injected_posts
        .into_iter()
        .enumerate()
        .map(|(idx, post)| {
            let post = substitute_summary_params(post, &replacements);
            // Slice 2: the clause leaves as the implication the callee proved.
            match if idx == last_idx { guard.take() } else { guard.clone() } {
                Some(antecedent) => Formula::Implies(Box::new(antecedent), Box::new(post)),
                None => post,
            }
        })
        .collect()
}

pub(super) fn replacements_without_bound_vars<'a>(
    replacements: &'a [(String, Formula)],
    bindings: &[(Symbol, Sort)],
) -> std::borrow::Cow<'a, [(String, Formula)]> {
    if !replacements
        .iter()
        .any(|(formal, _)| bindings.iter().any(|(bound, _)| bound.as_str() == formal))
    {
        return std::borrow::Cow::Borrowed(replacements);
    }
    std::borrow::Cow::Owned(
        replacements
            .iter()
            .filter(|(formal, _)| !bindings.iter().any(|(bound, _)| bound.as_str() == formal))
            .cloned()
            .collect(),
    )
}

/// [`generate_callsite_precondition_vcs`] into the caller's context `rows` (T3 C07p, design
/// D-VC-1): every row is interned through the row oracle and the rows are returned as
/// generated.
pub fn generate_callsite_precondition_vcs_rows(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    rows: &mut trust_types::vc_context::VcContext,
) -> Vec<VerificationCondition> {
    let vcs = generate_callsite_precondition_vcs(func, summaries);
    intern_eager_rows(rows, &vcs);
    vcs
}

/// [`generate_callsite_precondition_vcs_attributed`] into the caller's context `rows` (T3
/// C07p): each attributed row's VC is interned through the row oracle, and the attributed
/// rows are returned as generated.
pub fn generate_callsite_precondition_vcs_attributed_rows(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    rows: &mut trust_types::vc_context::VcContext,
) -> Vec<(VerificationCondition, Formula, Vec<Formula>)> {
    let attributed = generate_callsite_precondition_vcs_attributed(func, summaries);
    intern_eager_rows(rows, attributed.iter().map(|(vc, _, _)| vc));
    attributed
}
