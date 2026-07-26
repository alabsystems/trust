// Callsite precondition obligations: the callee's `requires` clause rewritten
// in terms of the caller's actuals. The rebinding is capture-avoiding because a
// callee parameter name can collide with a caller local, and a naive
// substitution would silently prove the wrong proposition.

use super::*;

pub fn generate_callsite_precondition_vcs(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> Vec<VerificationCondition> {
    if let Err(error) = crate::validate_function(func) {
        return vec![malformed_trust_ir_vc(func, &error)];
    }

    // verifier-perf (whole-function gate): an over-budget recursive-datatype function
    // explodes the `StmtVersionCtx::build` oracle / guard machinery below, and its own
    // `generate_vcs` already degrades it wholesale to a single Unknown. Emit NO callsite
    // precondition VCs for it. SOUNDNESS: DROP-ONLY — the whole function is already
    // fail-closed to Unknown, so withholding its (extra) callsite obligations cannot
    // manufacture a PROVE; it can only leave the function Unknown, which it already is.
    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    // The caller's own Requires clauses become guards in this lane.  Use the
    // same sanitized view as body VC generation so mathematical-Int arithmetic
    // can never be admitted as a callsite premise.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    let guard_paths_map = v2_build_path_guard_map(func);
    let semantic_guards = build_semantic_guard_map(func);
    // Cross-block PATH DEFINITIONS (`_7 == 4 * m` computed blocks before the
    // call): without them a callee precondition over a value THREADED from an
    // earlier block is refuted with the temp free (`_7 = 0` while `m = 2`).
    // Same machinery as the postcondition lane; live-filtered per call block.
    let path_definition_map = v2_build_path_definition_map(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    // Function-wide invariant facts (min/max result bounds, cast bounds, …):
    // unconditionally true, so sound in every callsite obligation. Without them
    // `f(1, x.max(1))` cannot discharge a callee `requires(lo <= hi)` — the
    // `max` result is an unmodeled call dest, free in ¬P[σ], and the VC is
    // spuriously SAT (a false refutation minting a VIOLATION row).
    let global_facts = build_global_invariant_facts(func);
    // The caller's OWN `#[requires]` over never-reassigned formals — entry facts
    // valid at every program point, so sound in every callsite obligation (see
    // `stable_caller_preconditions`). Without them `#[requires(lo <= hi)]`
    // cannot discharge a callee `requires(lo <= hi)` over σ-rooted `lo`/`hi`.
    let own_preconditions = stable_caller_preconditions(func);
    // F5: one shared float-tracer context for the structural interval-dominance
    // skip below (the guard-map cache is per-function).
    let float_ctx = FloatRangeCtx::new(func, Some(summaries));

    // `TRUST_PRECOND_DEBUG=1`: the PRODUCTION-lane twin of the attributed
    // producer's per-callsite diagnostic (this producer is the one the
    // compiler's whole-function VC pipeline drives). Diagnostic only.
    let precond_debug = std::env::var("TRUST_PRECOND_DEBUG").is_ok();

    let mut vcs = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee_name, args, span, .. } = &block.terminator else {
            continue;
        };
        let Some(summary) = summaries.get(callee_name) else {
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

        if !summary.preconditions.is_empty() && summary.param_names.len() != args.len() {
            vcs.push(VerificationCondition {
                kind: VcKind::UnsupportedMir {
                    kind: "SummaryArityMismatch".to_string(),
                    detail: format!(
                        "callee `{callee_name}` summary has {} formal parameter(s), call has {} argument(s)",
                        summary.param_names.len(),
                        args.len()
                    ),
                },
                function: func.name.as_str().into(),
                location: span.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
            continue;
        }

        let mut replacements: Vec<(String, Formula)> = summary
            .param_names
            .iter()
            .zip(args.iter())
            .map(|(formal, actual)| (formal.clone(), sigma_actual_formula(func, formal, actual)))
            .collect();
        // Trust (piece #8): σ-render `<formal>__slice_len` for slice/array formals
        // (parallel to the attributed producer, so both stay identical).
        append_length_replacements(func, summary, args, &mut replacements);

        for precondition in &summary.preconditions {
            if contracts::formula_uses_unmodeled_machine_arithmetic(precondition) {
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
            if precondition_interval_dominance(
                &float_ctx,
                block.id,
                precondition,
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
            let substituted = substitute_summary_params(precondition, &replacements);
            let mut formula = Formula::Not(Box::new(substituted));

            // Same-block STATEMENT DEFS (`_7 = 4 * m`), conjoined exactly like
            // the UnboundedAllocation lane does: without them a callee
            // `requires(2m <= 4m)` at `f(2*m, 4*m)` is refuted with the mul
            // temps FREE (`_7 = 0` while `m = 2`). Establish-versioned names
            // are bridged to ¬P[σ]'s bare spellings by the SSA normalization
            // at the end of this loop body.
            formula = v2_formula_with_block_defs(func, block, formula);

            // Cross-block path definitions, live-filtered against this block's
            // own redefs and terminator kills (the postcondition lane's
            // discipline). Spliced flat below by the sem-guard flatten.
            if let Some(path_defs) = path_definition_map.get(&block.id)
                && !path_defs.is_empty()
            {
                let mut live = v2_live_path_defs(func, block, path_defs);
                let term_defs: FxHashSet<String> =
                    terminator_def_names(func, block).into_iter().collect();
                if !term_defs.is_empty() {
                    live.retain(|f| formula_survives_redefs(f, &term_defs));
                }
                if !live.is_empty() {
                    // Trust: restore R1 recursion inductive-bound fact (regression from
                    // 52b31a7d2a). `formula` is already the block-def-wrapped
                    // `And([arg-defs…, ¬P[σ]])`; pushing it WHOLE nests `¬P[σ]` a level deep,
                    // and when no later sem-guard flatten runs (a guarded recursive call has
                    // path defs but no semantic guards) the nesting survives to the emitted VC
                    // — so the R1 discharge gate's direct-conjunct check fails. Splice the
                    // inner conjuncts flat instead (pure `∧` associativity, verdict-identical).
                    match formula {
                        Formula::And(inner) => live.extend(inner),
                        other => live.push(other),
                    }
                    formula = Formula::And(live);
                }
            }

            if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
                formula = v2_formula_with_path_guards(func, &sv, block_guard_paths, formula);
            }

            if let Some(sem_guards) = semantic_guards.get(&block.id)
                && !sem_guards.is_empty()
            {
                let mut conjuncts = sem_guards.clone();
                // BARE-named variants for SSA call-dest facts: a
                // `version_terminator_dest_fact` guard names its subject
                // `_5#s0_t`, while ¬P[σ] renders the same SSA local bare
                // (`_5`) — conjoin the identity-renamed copy so the fact
                // actually constrains the obligation. See
                // `bare_ssa_guard_variant` for the SSA soundness argument.
                conjuncts.extend(sem_guards.iter().filter_map(|g| bare_ssa_guard_variant(func, g)));
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
                match formula {
                    Formula::And(inner) => conjuncts.extend(inner),
                    other => conjuncts.push(other),
                }
                formula = Formula::And(conjuncts);
            }

            // Global invariant facts, spliced flat for the same reason as the
            // semantic guards above (¬P[σ] must stay a DIRECT conjunct).
            if !global_facts.is_empty() {
                let mut conjuncts = global_facts.clone();
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
                let mut conjuncts = own_preconditions.clone();
                match formula {
                    Formula::And(inner) => conjuncts.extend(inner),
                    other => conjuncts.push(other),
                }
                formula = Formula::And(conjuncts);
            }

            // COMPLETE alias post-pass (see `freshen_aliasing_opaque_occurrences`): per-occurrence
            // freshen every guard/semantic-fact opaque symbol the by-name interning collapsed, so
            // two distinct const-generic / unevaluated-const reads can never alias into one SMT
            // symbol (which would fabricate an equality that spuriously discharges the VC). The σ
            // namespace (`__trust_sigma_*`) is disjoint and left intact.
            let occ = std::cell::Cell::new(0u32);
            let formula = freshen_aliasing_opaque_occurrences(&formula, &occ);
            // Collapse SSA version tokens so establish-versioned block defs
            // (`_7#s0_1 == 4 * m`) bind ¬P[σ]'s bare `_7`. ¬P[σ] itself uses
            // bare σ names (no `#`), so it is untouched.
            let formula = normalize_ssa_version_tokens(func, &formula);

            vcs.push(VerificationCondition {
                kind: VcKind::Precondition { callee: callee_name.clone() },
                function: func.name.as_str().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        }
    }
    vcs
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
    if let Err(error) = crate::validate_function(func) {
        return vec![(malformed_trust_ir_vc(func, &error), Formula::Bool(true), Vec::new())];
    }

    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    let guard_paths_map = v2_build_path_guard_map(func);
    let semantic_guards = build_semantic_guard_map(func);
    // Cross-block path definitions — identical to the non-attributed producer.
    let path_definition_map = v2_build_path_definition_map(func);
    let sv = StmtVersionCtx::build(func);
    // Same fact set the non-attributed producer conjoins — the two assemblies
    // must stay IDENTICAL (see the doc above).
    let global_facts = build_global_invariant_facts(func);
    // Same stable own-precondition set the non-attributed producer conjoins
    // (see `stable_caller_preconditions` for the gate and for why NOT
    // `conjoin_preconditions_versioned` — its unconditional version-rename
    // would rewrite ¬P[σ] and break the `not_p` structural match below).
    let own_preconditions = stable_caller_preconditions(func);
    // F5 skip context — identical to the non-attributed producer.
    let float_ctx = FloatRangeCtx::new(func, Some(summaries));

    // `TRUST_PRECOND_DEBUG=1`: per-callsite diagnostic for the F5/F6b
    // suppression seam (which callee summaries the producer actually sees and
    // why a precondition VC was minted instead of suppressed). Diagnostic
    // only — no verdict change.
    let precond_debug = std::env::var("TRUST_PRECOND_DEBUG").is_ok();

    let mut out = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee_name, args, span, .. } = &block.terminator else {
            continue;
        };
        let Some(summary) = summaries.get(callee_name) else {
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

        if !summary.preconditions.is_empty() && summary.param_names.len() != args.len() {
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
                    function: func.name.as_str().into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                Formula::Bool(true),
                Vec::new(),
            ));
            continue;
        }

        let mut replacements: Vec<(String, Formula)> = summary
            .param_names
            .iter()
            .zip(args.iter())
            .map(|(formal, actual)| (formal.clone(), sigma_actual_formula(func, formal, actual)))
            .collect();
        // Trust (piece #8): render `<formal>__slice_len` for each slice/array formal
        // from the ACTUAL argument's length, so a length-relationship precondition
        // (`n <= arr__slice_len`) can discharge at this caller.
        append_length_replacements(func, summary, args, &mut replacements);

        for precondition in &summary.preconditions {
            if contracts::formula_uses_unmodeled_machine_arithmetic(precondition) {
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
            if precondition_interval_dominance(
                &float_ctx,
                block.id,
                precondition,
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
            // The INDEPENDENT pre-image: same fn + same σ the obligation is built from.
            let substituted = substitute_summary_params(precondition, &replacements);
            let not_p = Formula::Not(Box::new(substituted.clone()));
            let mut formula = not_p.clone();

            // Same-block STATEMENT DEFS — identical to the non-attributed
            // producer (they surface in `guards` for the R1 gate; the flatten
            // below keeps ¬P[σ] a direct conjunct).
            formula = v2_formula_with_block_defs(func, block, formula);

            // Cross-block path definitions, live-filtered against this block's
            // own redefs and terminator kills (the postcondition lane's
            // discipline). Spliced flat below by the sem-guard flatten.
            if let Some(path_defs) = path_definition_map.get(&block.id)
                && !path_defs.is_empty()
            {
                let mut live = v2_live_path_defs(func, block, path_defs);
                let term_defs: FxHashSet<String> =
                    terminator_def_names(func, block).into_iter().collect();
                if !term_defs.is_empty() {
                    live.retain(|f| formula_survives_redefs(f, &term_defs));
                }
                if !live.is_empty() {
                    // Trust: restore R1 recursion inductive-bound fact (regression from
                    // 52b31a7d2a). `formula` is already the block-def-wrapped
                    // `And([arg-defs…, ¬P[σ]])`; pushing it WHOLE nests `¬P[σ]` a level deep,
                    // and when no later sem-guard flatten runs (a guarded recursive call has
                    // path defs but no semantic guards) the nesting survives to the emitted VC
                    // — so the R1 discharge gate's direct-conjunct check fails. Splice the
                    // inner conjuncts flat instead (pure `∧` associativity, verdict-identical).
                    match formula {
                        Formula::And(inner) => live.extend(inner),
                        other => live.push(other),
                    }
                    formula = Formula::And(live);
                }
            }

            if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
                formula = v2_formula_with_path_guards(func, &sv, block_guard_paths, formula);
            }
            if let Some(sem_guards) = semantic_guards.get(&block.id)
                && !sem_guards.is_empty()
            {
                let mut conjuncts = sem_guards.clone();
                // BARE-named variants for SSA call-dest facts: a
                // `version_terminator_dest_fact` guard names its subject
                // `_5#s0_t`, while ¬P[σ] renders the same SSA local bare
                // (`_5`) — conjoin the identity-renamed copy so the fact
                // actually constrains the obligation. See
                // `bare_ssa_guard_variant` for the SSA soundness argument.
                conjuncts.extend(sem_guards.iter().filter_map(|g| bare_ssa_guard_variant(func, g)));
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
                match formula {
                    Formula::And(inner) => conjuncts.extend(inner),
                    other => conjuncts.push(other),
                }
                formula = Formula::And(conjuncts);
            }

            // Global invariant facts, spliced flat — identical to the
            // non-attributed producer. They surface in `guards` below as
            // legitimate vcgen-emitted context for the discharge gate.
            if !global_facts.is_empty() {
                let mut conjuncts = global_facts.clone();
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
                let mut conjuncts = own_preconditions.clone();
                match formula {
                    Formula::And(inner) => conjuncts.extend(inner),
                    other => conjuncts.push(other),
                }
                formula = Formula::And(conjuncts);
            }

            // COMPLETE alias post-pass (see `freshen_aliasing_opaque_occurrences`): freshen guard /
            // semantic-fact opaque symbols per occurrence BEFORE extracting `guards`, so the gate's
            // `allowed_guards` and the certified `vc.formula` agree and no aliased equality can
            // fabricate a discharge. `¬P[σ]` (== `not_p`, the gate's structural anchor) uses the
            // disjoint `__trust_sigma_*` namespace and is preserved exactly, so the membership
            // check below still matches.
            let occ = std::cell::Cell::new(0u32);
            let formula = freshen_aliasing_opaque_occurrences(&formula, &occ);
            // Collapse SSA version tokens — identical to the non-attributed
            // producer; runs BEFORE the guards extraction, and never renames
            // `not_p` (bare σ names carry no `#`), so the membership check
            // below still matches.
            let formula = normalize_ssa_version_tokens(func, &formula);

            // Top-level guard conjuncts admissible for the gate: ONLY when `¬P[σ]` is a
            // DIRECT conjunct of a flat `And` (or the bare formula). Nested `And` / `Or`
            // ⇒ [] (the gate then rejects via its `not_p` membership check).
            let guards: Vec<Formula> = match &formula {
                f if *f == not_p => Vec::new(),
                Formula::And(cs) if cs.contains(&not_p) => {
                    cs.iter().filter(|c| **c != not_p).cloned().collect()
                }
                _ => Vec::new(),
            };

            out.push((
                VerificationCondition {
                    kind: VcKind::Precondition { callee: callee_name.clone() },
                    function: func.name.as_str().into(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                },
                substituted,
                guards,
            ));
        }
    }
    for (vc, _, _) in &mut out {
        vc.function = func.def_path.as_str().into();
    }
    out
}

/// Split a solver variable name into `(base, projection-suffix)` at the FIRST
/// projection token (`.` field, `*` deref, `[` index, `@` downcast), the exact
/// tokens `place_to_var_name` emits. Returns `None` for a bare name (no
/// projection) — those are handled by the whole-name substitution path — and for
/// a name that starts with a projection token (no base to substitute).
pub(super) fn split_projection_base(name: &str) -> Option<(&str, &str)> {
    let idx = name.find(|c: char| matches!(c, '.' | '*' | '[' | '@'))?;
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

pub(crate) fn substitute_summary_params(
    formula: &Formula,
    replacements: &[(String, Formula)],
) -> Formula {
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
    }

    match formula {
        Formula::Forall(bindings, body) => {
            // Capture-avoiding: rename any binder that would capture a free var of
            // a replacement value before substituting (soundness, round-7).
            let (bindings, body) = capture_avoiding_rebind(bindings, body, replacements);
            let scoped_replacements = replacements_without_bound_vars(replacements, &bindings);
            Formula::Forall(
                bindings,
                Box::new(substitute_summary_params(&body, &scoped_replacements)),
            )
        }
        Formula::Exists(bindings, body) => {
            let (bindings, body) = capture_avoiding_rebind(bindings, body, replacements);
            let scoped_replacements = replacements_without_bound_vars(replacements, &bindings);
            Formula::Exists(
                bindings,
                Box::new(substitute_summary_params(&body, &scoped_replacements)),
            )
        }
        _ => formula
            .clone()
            .map_children(&mut |child| substitute_summary_params(&child, replacements)),
    }
}

/// Collect the name of every `Var` node in `formula`. Conservative: it also
/// descends into nested binders, but over-collection only triggers extra,
/// always-sound alpha-renaming.
pub(super) fn collect_var_names(formula: &Formula, out: &mut FxHashSet<String>) {
    if let Some(name) = formula.var_name() {
        out.insert(name.to_string());
    }
    for child in formula.children() {
        collect_var_names(child, out);
    }
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
    bindings: &[(Symbol, Sort)],
    body: &Formula,
    replacements: &[(String, Formula)],
) -> (Vec<(Symbol, Sort)>, Formula) {
    // Only replacements that actually apply in this scope can cause capture.
    let active = replacements_without_bound_vars(replacements, bindings);
    let mut danger: FxHashSet<String> = FxHashSet::default();
    for (_, value) in &active {
        collect_var_names(value, &mut danger);
    }
    if !bindings.iter().any(|(s, _)| danger.contains(s.as_str())) {
        return (bindings.to_vec(), body.clone());
    }

    // Names to avoid when minting fresh binder names.
    let mut used: FxHashSet<String> = danger.clone();
    collect_var_names(body, &mut used);
    for (s, _) in bindings {
        used.insert(s.as_str().to_string());
    }

    let mut new_bindings: Vec<(Symbol, Sort)> = Vec::with_capacity(bindings.len());
    let mut renamed_body = body.clone();
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
            renamed_body = substitute_summary_params(
                &renamed_body,
                &[(sym.as_str().to_string(), Formula::var(&fresh, sort.clone()))],
            );
            new_bindings.push((Symbol::intern(&fresh), sort.clone()));
        } else {
            new_bindings.push((sym.clone(), sort.clone()));
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
///   evidence-id strings are deliberately ignored. Production currently has no
///   minter, so this remains false until trust-vcgen can verify a non-forgeable
///   compiler carrier; the crate-private test mint exercises the consumer seal.
///   This is STRICTLY STRONGER than `proved`: a sealed-but-unverified or
///   open-world `dyn` summary is `proved` for precondition CHECKS yet must not
///   have its postcondition ASSUMED;
/// - non-empty `postconditions` — otherwise there is nothing to inject;
/// - projection-free, single-static-assignment `dest` — the same gate the stdlib
///   min/max facts use, so a `&mut`-reassigned dest cannot leave a stale bound;
/// - arity match — otherwise the formal→arg rebinding would be ill-formed.
pub(crate) fn callee_postcondition_is_injectable(
    func: &VerifiableFunction,
    dest: &Place,
    summary: &crate::modular::FunctionSummary,
    arg_count: usize,
) -> bool {
    summary.has_reusable_postcondition_evidence()
        && dest.projections.is_empty()
        && summary.param_names.len() == arg_count
        && is_single_static_assignment(func, dest.local)
        // At least one postcondition must be fully rebindable, else nothing is
        // injected (and `assumptions_injected` would over-count).
        && summary
            .postconditions
            .iter()
            .any(|p| {
                !contracts::formula_uses_unmodeled_machine_arithmetic(p)
                    && postcondition_rebindable(p, &summary.param_names)
            })
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
    post.free_variables().iter().all(|v| v == "_0" || param_names.iter().any(|p| p == v))
}

pub(crate) fn rebind_callee_postconditions(
    func: &VerifiableFunction,
    args: &[Operand],
    dest: &Place,
    summary: &crate::modular::FunctionSummary,
) -> Vec<Formula> {
    let mut replacements: Vec<(String, Formula)> = summary
        .param_names
        .iter()
        .zip(args.iter())
        .map(|(formal, actual)| (formal.clone(), operand_to_formula(func, actual)))
        .collect();
    // Map the callee return symbol `_0` to the caller's destination place.
    let dest_name = place_to_var_name(func, dest);
    let dest_sort = crate::place_sort(func, dest).unwrap_or(Sort::Int);
    replacements.push(("_0".to_string(), Formula::var(&dest_name, dest_sort)));

    summary
        .postconditions
        .iter()
        // A proof produced for mathematical-Int arithmetic is not authority for
        // a fixed-width Rust postcondition at the call site.
        .filter(|post| !contracts::formula_uses_unmodeled_machine_arithmetic(post))
        // Drop any clause with a non-rebindable free var BEFORE substitution — see
        // `postcondition_rebindable`. Without this filter a stray callee symbol
        // captures a same-named caller local and can false-PROVE.
        .filter(|post| postcondition_rebindable(post, &summary.param_names))
        .map(|post| substitute_summary_params(post, &replacements))
        .collect()
}

pub(super) fn replacements_without_bound_vars(
    replacements: &[(String, Formula)],
    bindings: &[(Symbol, Sort)],
) -> Vec<(String, Formula)> {
    replacements
        .iter()
        .filter(|(formal, _)| !bindings.iter().any(|(bound, _)| bound.as_str() == formal))
        .cloned()
        .collect()
}
