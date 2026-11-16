// Contract obligations: `requires`/`ensures` clauses turned into VCs, and the
// return-slot pinning that makes a postcondition mentioning the return value
// refer to the value actually returned on each path.

use super::*;

mod return_metadata;
#[cfg(test)]
mod return_metadata_tests;
// INTRINSIC-RESIDUAL-1: the call twin of the free-return-value tripwire.
#[cfg(test)]
mod call_return_tripwire_tests;

/// How many enumerated return PATHS a single `Return`-block predecessor may be
/// split into, one postcondition row per path (see the per-path split in
/// [`generate_v2_contract_vcs_impl`]).
///
/// The guard walk itself keeps at most `safety::MAX_PATHS_PER_BLOCK` (64) paths
/// per block, and splitting 64 ways would multiply this clause's solver calls by
/// 64 for a shape no author writes. Past the cap the row keeps TODAY'S single
/// `Or([per-path term, ..])` spelling, which is exactly the behaviour every row
/// had before the split existed — so the cap can only cost capability, never
/// soundness.
///
/// KILL SWITCH. Setting this to `1` makes the admitting range `2..=1` empty, so
/// no split ever fires and every emitted row is byte-identical to the pre-split
/// compiler. That is the one-line revert if the split ever has to be backed out
/// without reverting the tests and docs; `per_path_postcondition_tests`'s two
/// `row_count_*` tests are the ones that then go red, by design.
pub(super) const POSTCONDITION_PATH_SPLIT_CAP: usize = 8;

/// Summary-aware contract generation: the caller's OWN declared `ensures` (the
/// `VcKind::Postcondition` lane) consults the summary-aware guard map, so the
/// canonical separate-compilation case — proving `caller ensures P` from a
/// callee's contract — discharges. `None` selects canonical non-summary behavior.
pub(super) fn generate_v2_contract_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<VerificationCondition> {
    // Len-witness debug context: tag every `LENWITNESS:` line emitted while this
    // function's contract VCs are generated (env-gated; no-op when unset).
    lenwitness_dbg_set_fn(&func.def_path);
    let contract_metadata =
        if func.spec.is_empty() { None } else { Some(func.spec.to_contract_metadata()) };

    let mut vcs = Vec::new();
    contracts::check_contracts(func, &mut vcs);
    vcs.extend(spec_parser::generate_spec_vcs(func));

    // `func.preconditions` is the semantic entry-hypothesis carrier, not a
    // source-clause provenance carrier.  Besides authored Requires it contains
    // compiler facts that hold by construction (integer ranges, discriminant
    // ranges, char validity) and may temporarily contain an inferred
    // strengthening hypothesis.  Emitting a self-`Precondition`/`Bool(false)`
    // row for each formula fabricates definition-entry bookkeeping with no
    // source identity and no authority that can distinguish it from a recursive
    // self-call obligation.
    //
    // Authored Requires bookkeeping is already emitted by the two provenance-
    // owning lanes above: `check_contracts` for raw `Contract` clauses and
    // `generate_spec_vcs` for compatibility `FunctionSpec` clauses.  Real
    // caller obligations remain in the modular/callsite generators.  Formula-
    // only hypotheses therefore emit no standalone row here; they still flow
    // unchanged through every body VC's entry context.

    // Trust: Per-Return-block postcondition VCs. We process both the
    // declared `func.postconditions` and any `Ensures` contracts (parsed
    // from their string body). When both sources reference the same
    // postcondition, the placeholder `Formula::Not(parsed)` VC produced by
    // `check_contracts` is *replaced* by the body-aware VCs generated
    // here. Without that swap, the placeholder fires with no knowledge of
    // the return-block dataflow and the obligation is always SAT (refuted).
    if func.postconditions.is_empty()
        && !func.contracts.iter().any(|c| matches!(c.kind, ContractKind::Ensures))
    {
        return vcs;
    }

    enum PostOrigin<'a> {
        FormulaDebug,
        BorrowedText(&'a str),
    }
    impl PostOrigin<'_> {
        fn into_owned_string(self, post: &Formula) -> String {
            match self {
                Self::FormulaDebug => format!("{post:?}"),
                Self::BorrowedText(body) => body.to_string(),
            }
        }
    }

    let parsed_ensures: Vec<(usize, &str, &SourceSpan, Formula)> = func
        .contracts
        .iter()
        .enumerate()
        .filter_map(|(contract_index, contract)| {
            if !matches!(contract.kind, ContractKind::Ensures) {
                return None;
            }
            let body = contract
                .body
                .strip_prefix(contracts::LOWERED_CONTRACT_PREFIX)
                .unwrap_or(&contract.body);
            // Extraction rebinds an admitted `xs.len()` leaf (`xs__len`) to the
            // canonical `xs__slice_len` in `func.postconditions`
            // (`rebind_postcondition_lengths`); re-read the raw text copy the same way,
            // and ONLY for a base extraction rebound, or it would look like a second
            // clause over a free `xs__len`.
            let parsed =
                trust_types::parse_spec_expr(body).map(|parsed| rebind_text_lengths(func, parsed))?;
            Some((contract_index, body, &contract.span, parsed))
        })
        .collect();

    let mut matched_ensures = vec![false; parsed_ensures.len()];
    let mut posts: Vec<(Formula, PostOrigin<'_>, SourceSpan, Option<usize>)> =
        Vec::with_capacity(func.postconditions.len() + parsed_ensures.len());
    for f in &func.postconditions {
        let mut first_idx = None;
        let mut multiple = false;
        for (pos, (idx, _, _, parsed)) in parsed_ensures.iter().enumerate() {
            if parsed_clause_matches_typed(parsed, f) {
                matched_ensures[pos] = true;
                if first_idx.is_none() {
                    first_idx = Some(*idx);
                } else {
                    multiple = true;
                }
            }
        }
        posts.push((
            f.clone(),
            PostOrigin::FormulaDebug,
            func.span.clone(),
            if multiple { None } else { first_idx },
        ));
    }
    let declared_post_len = posts.len();
    for (pos, (contract_index, body, span, parsed)) in parsed_ensures.into_iter().enumerate() {
        // Sort-exact equality here made every `bool` clause fail to recognize
        // its own typed lowering, appending a SECOND, ill-sorted copy of the
        // same postcondition. That copy cannot lower to typed TrustIr, so it
        // carries no `trust.vc.formula.payload` and lands as a fail-closed
        // Unknown that also denies the whole function native evidence. Match
        // modulo the parser's `Sort::Int` sentinel so the typed clause — the
        // type-faithful reading, and the one that actually gets solved — is
        // recognized as already present.
        if !matched_ensures[pos]
            && !posts[declared_post_len..]
                .iter()
                .any(|(f, _, _, _)| parsed_clause_matches_typed(&parsed, f))
        {
            posts.push((
                parsed,
                PostOrigin::BorrowedText(body),
                span.clone(),
                Some(contract_index),
            ));
        }
    }

    if posts.is_empty() {
        return vcs;
    }

    // SOUNDNESS (ny selfcheck over-refutation): split off postconditions whose
    // formula references SYNTHETIC SPEC-MODEL terms (`{base}_discr` /
    // `{base}_value*` / `{base}_sign` / `.__trust_ok_i` — the lowered
    // `matches!(r, Ok(..) if ..)` / `is_ok` / `unwrap` / `is_positive` idioms).
    // This lane grounds NONE of those names: the return-value pins below connect
    // `_0`, never `_0__discr`/`_0__value*`, so `Not(post)` stays satisfiable by
    // havoc REGARDLESS of the body and the obligation is reported Failed with a
    // counterexample MINTED over the under-constrained encoding — not a program
    // trace. Such a postcondition must land as the fail-closed NON-REFUTABLE
    // Unknown (below), never as a refutable per-return-block VC, and never be
    // silently dropped (a false-PROVE).
    // Names the body-aware lane can now GROUND (Option/Result-return
    // `_0__discr` — plus `_0__value` for an integer payload — when every return
    // path pins them in-body; empty otherwise — see
    // `enum_return_grounded_model_vars`). Subtracting these from the per-post
    // ungrounded set lets an Option<integer>/Result postcondition survive into
    // `explicit_postconditions` so it reaches the pin loop's discr/value pins,
    // instead of being shunted to fail-closed Unknown. Compared on BASE name
    // (strip any `#version` token) since the return-slot terms are unversioned.
    let lenwitness_dbg = super::witness_grounding::lenwitness_debug();
    let mut any_spec_model_var = lenwitness_dbg;
    let mut any_enum_return_model_var = lenwitness_dbg;
    let mut any_len_witness_var = lenwitness_dbg;
    let mut any_ord_witness_var = false;
    for (f, _, _, _) in &posts {
        trust_types::visit_formula_nodes(f, &mut |node| {
            let Formula::Var(name, _) = node else { return };
            if !contracts::is_spec_model_var(name) {
                return;
            }
            any_spec_model_var = true;
            let base = name.split('#').next().unwrap_or(name);
            if base == "_0__discr" || base == "_0__value" {
                any_enum_return_model_var = true;
            } else if base.starts_with("_0__value.__trust_ok_") {
                any_ord_witness_var = true;
            } else if base.starts_with("_0__value.") && base.ends_with("__len") {
                any_len_witness_var = true;
            }
        });
    }
    let (groundable, len_pairs, len_groundable, ord_items, ord_groundable) = if any_spec_model_var {
        let groundable = if any_enum_return_model_var {
            enum_return_grounded_model_vars(func)
        } else {
            FxHashSet::default()
        };
        let post_refs: Vec<&Formula> = if any_len_witness_var || any_ord_witness_var {
            posts.iter().map(|(f, _, _, _)| f).collect()
        } else {
            Vec::new()
        };
        // Len-witness lane (b62): payload-component length pairs whose equality every
        // return path establishes in-body. The same resolver supplies the pins below.
        let len_pairs = if any_len_witness_var {
            len_witness_credited_pairs(func, &post_refs)
        } else {
            Vec::new()
        };
        let len_groundable: FxHashSet<String> =
            len_pairs.iter().flat_map(|(a, b)| [a.name.clone(), b.name.clone()]).collect();
        // Ordering-witness lane (b62 F4), likewise gated across every return path (pair
        // terms only, on a compiler-established order-consistent payload type; the sign
        // half is retired: ORD-WITNESS-CONSISTENT-1).
        let ord_items = if any_ord_witness_var {
            ordering_witness_credited_items(func, &post_refs)
        } else {
            Vec::new()
        };
        let ord_groundable: FxHashSet<String> =
            ord_items.iter().flat_map(OrdWitnessItem::model_names).collect();
        (groundable, len_pairs, len_groundable, ord_items, ord_groundable)
    } else {
        (
            FxHashSet::default(),
            Vec::new(),
            FxHashSet::default(),
            Vec::new(),
            FxHashSet::default(),
        )
    };
    let mut explicit_postconditions: Vec<(Formula, Option<usize>, bool)> =
        Vec::with_capacity(posts.len());
    let mut ungrounded_posts: Vec<(Vec<String>, String, SourceSpan, Option<usize>)> = Vec::new();
    for (post, origin, span, source_contract_index) in posts {
        // An arithmetic-bearing clause the Machine{w} lane admits
        // (`machine_faithful_clause_admissible`: one shared declared machine
        // width, wrap-exact fragment, only spec `%` by a total literal divisor)
        // enters the refutable
        // body-aware lane — flagged so the FINAL assembled VC is translated
        // wholesale into declared-width QF_BV before it is emitted (the
        // ratified L1 rule 4 type-directed reading; the mathematical-Int
        // spelling of machine arithmetic below is exactly the confirmed
        // `result + 1 > result` false-proof vector and must never reach a
        // solver). Every other authored machine-arithmetic clause keeps its
        // existing fail-closed lane. Raw Contract / FunctionSpec clauses
        // already emitted their own visible Unknown above. Formula-only
        // callers have no such producer, however, and this helper is also
        // exercised directly by the ordering-witness soundness gates. Preserve
        // one non-refutable row here instead of silently dropping their
        // clause. When synthetic model names are present, retain the more
        // precise ungrounded row (and its exact missing-name list); otherwise
        // use the general unverifiable specification row.
        if contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, &post) {
            if contracts::machine_faithful_clause_admissible(func, &post) {
                let ungrounded = if any_spec_model_var {
                    contracts::ungrounded_spec_model_vars(&post)
                } else {
                    Vec::new()
                };
                if ungrounded.is_empty() {
                    explicit_postconditions.push((post, source_contract_index, true));
                } else {
                    let origin_str = origin.into_owned_string(&post);
                    ungrounded_posts.push((ungrounded, origin_str, span, source_contract_index));
                }
                continue;
            }
            if !parsed_source_clause_matches(func, ContractKind::Ensures, &post) {
                let ungrounded = if any_spec_model_var {
                    contracts::ungrounded_spec_model_vars(&post)
                } else {
                    Vec::new()
                };
                let origin_str = origin.into_owned_string(&post);
                if ungrounded.is_empty() {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        span,
                        "formula-only ensures uses unmodeled fixed-width machine arithmetic",
                        &origin_str,
                        contract_metadata_with_source_index(
                            contract_metadata,
                            source_contract_index,
                        ),
                    ));
                } else {
                    ungrounded_posts.push((ungrounded, origin_str, span, source_contract_index));
                }
            }
            continue;
        }
        if !any_spec_model_var {
            explicit_postconditions.push((post, source_contract_index, false));
            continue;
        }
        let ungrounded: Vec<String> = contracts::ungrounded_spec_model_vars(&post)
            .into_iter()
            .filter(|n| {
                let base = n.split('#').next().unwrap_or(n);
                !groundable.contains(base)
                    && !len_groundable.contains(base)
                    && !ord_groundable.contains(base)
            })
            .collect();
        if ungrounded.is_empty() {
            explicit_postconditions.push((post, source_contract_index, false));
        } else {
            let origin_str = origin.into_owned_string(&post);
            ungrounded_posts.push((ungrounded, origin_str, span, source_contract_index));
        }
    }

    // Drop the placeholder Postcondition VCs that `check_contracts` /
    // `generate_spec_vcs` emitted (replaced below with body-aware ones), AND the
    // fail-closed SpecModelUngrounded rows those lanes emitted for this same
    // contract set (re-emitted below exactly once per ungrounded postcondition,
    // so the obligation is never duplicated and never lost).
    vcs.retain(|vc| {
        !matches!(vc.kind, VcKind::Postcondition)
            && !matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == contracts::SPEC_MODEL_UNGROUNDED_KIND)
    });

    for (ungrounded, origin, span, source_contract_index) in &ungrounded_posts {
        vcs.push(contracts::spec_model_ungrounded_vc(
            func,
            span.clone(),
            origin,
            ungrounded,
            contract_metadata_with_source_index(contract_metadata, *source_contract_index),
        ));
    }

    if explicit_postconditions.is_empty() {
        return vcs;
    }

    if !func
        .body
        .blocks
        .iter()
        .any(|b| matches!(&b.terminator, Terminator::Return | Terminator::TailCall { .. }))
    {
        return vcs;
    }

    let guard_paths_map_cell: std::cell::OnceCell<
        std::rc::Rc<FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>>>,
    > = std::cell::OnceCell::new();
    let sv_cell: std::cell::OnceCell<std::rc::Rc<StmtVersionCtx>> = std::cell::OnceCell::new();
    let path_definition_map_cell: std::cell::OnceCell<
        std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
    > = std::cell::OnceCell::new();
    let semantic_guards_cell: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let out_param_store_sorts_cell: std::cell::OnceCell<FxHashMap<String, Option<Sort>>> =
        std::cell::OnceCell::new();
    let dropped_requires_cell: std::cell::OnceCell<Vec<Formula>> = std::cell::OnceCell::new();
    let empty_kill: FxHashSet<String> = FxHashSet::default();

    // Trust: the postcondition parser models `result`/`_0` as a default
    // (Int) sort, but the return slot's true sort may differ — e.g. a
    // `-> bool` predicate `fn f(x) -> bool { x > 0 }`. Re-sort the postcond's
    // `_0` to the function's ACTUAL return sort so it unifies with the body's
    // typed return value; otherwise a `-> bool` postcondition like
    // `ret == (x > 0)` is false-refuted (the body fact `__ret == (x > 0)` is
    // Bool while the postcond's `_0` is Int — two disconnected variables).
    let ret_place = Place::local(0);
    let ret_sort = crate::place_sort(func, &ret_place).unwrap_or(Sort::Int);
    let ret_alias = place_to_var_name(func, &ret_place);
    let ret_subst = [("_0".to_string(), Formula::var_owned("_0".to_string(), ret_sort.clone()))];
    let ret_alias_subst = (ret_alias != "_0")
        .then(|| [(ret_alias.clone(), Formula::var_owned("_0".to_string(), ret_sort.clone()))]);
    let may_have_enum_return = !groundable.is_empty()
        || super::witness_grounding::body_may_have_std_enum_return(func)
        || super::witness_grounding::lenwitness_debug();
    let global_facts_cell: std::cell::OnceCell<std::rc::Rc<RowGlobalFacts>> =
        std::cell::OnceCell::new();
    let fn_sym: Symbol = func.name.as_str().into();
    let mut v2_preds: Option<std::rc::Rc<crate::fn_memo::V2Predecessors>> = None;
    let empty_clause_sorts: FxHashMap<String, Option<Sort>> = FxHashMap::default();

    struct PreparedPostcondition {
        raw_post: Formula,
        clause_metadata: Option<ContractMetadata>,
        machine_lane: bool,
        formula_refs_return_slot: bool,
        refs_mutated_param: bool,
        resorted_post: std::cell::OnceCell<Formula>,
        clause_sorts: std::cell::OnceCell<FxHashMap<String, Option<Sort>>>,
        base_clause_written_out_params: std::cell::OnceCell<Vec<String>>,
    }
    let mutated_param_places_cell: std::cell::OnceCell<super::callee_summaries::MutatedParamPlaces> =
        std::cell::OnceCell::new();
    let prepared_posts: Vec<PreparedPostcondition> = explicit_postconditions
        .into_iter()
        .map(|(raw_post, source_contract_index, machine_lane)| {
            let clause_metadata =
                contract_metadata_with_source_index(contract_metadata, source_contract_index);
            let formula_refs_return_slot = formula_references_return_slot(&raw_post);
            let refs_mutated_param =
                super::callee_summaries::postcondition_references_mutated_param_cached(
                    func,
                    &raw_post,
                    &mutated_param_places_cell,
                );
            PreparedPostcondition {
                raw_post,
                clause_metadata,
                machine_lane,
                formula_refs_return_slot,
                refs_mutated_param,
                resorted_post: std::cell::OnceCell::new(),
                clause_sorts: std::cell::OnceCell::new(),
                base_clause_written_out_params: std::cell::OnceCell::new(),
            }
        })
        .collect();

    for block in &func.body.blocks {
        if !matches!(&block.terminator, Terminator::Return | Terminator::TailCall { .. }) {
            continue;
        }

        let preds = v2_preds.get_or_insert_with(|| crate::fn_memo::v2_predecessors_or_build(func));
        let predecessors = preds.predecessors(func, block.id);
        let vc_blocks: Vec<&trust_types::BasicBlock> =
            if predecessors.is_empty() { vec![block] } else { predecessors };
        let metadata_pins: Vec<_> = vc_blocks
            .iter()
            .map(|predecessor| return_metadata::for_return_path(func, predecessor, block))
            .collect();
        let agg_operands_cell: std::cell::OnceCell<FxHashMap<String, Option<Sort>>> =
            std::cell::OnceCell::new();

        struct PreparedReturnPath {
            vc_block_span: SourceSpan,
            direct_return_pins: Vec<Formula>,
            unlowerable_return_assignment: bool,
            enum_return_pins: Vec<Formula>,
            witness_pins: Vec<Formula>,
            call_dest_return_pins: Vec<Formula>,
            arm_copy_pin: Option<(Vec<Formula>, bool)>,
            has_deref_load_return: bool,
            edge_guard: Option<Formula>,
            live_path_defs: Vec<Formula>,
            sem_conjuncts: Vec<Formula>,
            unmarked_sysroot_call: std::cell::OnceCell<bool>,
        }
        let prepared_paths: Vec<std::cell::OnceCell<PreparedReturnPath>> =
            (0..vc_blocks.len()).map(|_| std::cell::OnceCell::new()).collect();

        for prep in &prepared_posts {
            let clause_metadata = prep.clause_metadata.clone();
            let machine_lane = &prep.machine_lane;
            let formula_refs_return_slot = prep.formula_refs_return_slot;
            // A failed metadata relation is independently fatal to this
            // authored postcondition. Do this before the reassigned-parameter
            // shortcut and before any other return-pin producer: neither a
            // free clause nor a stale scalar pin can repair the missing value.
            if formula_refs_return_slot
                && let Some(reason) = metadata_pins.iter().find_map(|pin| match pin {
                    return_metadata::MetadataReturnPin::Unsupported(reason) => Some(*reason),
                    _ => None,
                })
            {
                vcs.push(contracts::spec_unverifiable_vc(
                    func,
                    v2_block_span(func, block),
                    reason,
                    &format!("{:?}", prep.raw_post),
                    clause_metadata,
                ));
                continue;
            }
            // SOUNDNESS (P0, hunt-6): a postcondition over a REASSIGNED by-value parameter would
            // be proved against the parameter's FINAL value, not its `ensures` ENTRY snapshot — a
            // false proof (`#[ensures(move |r| *r==a)] fn f(mut a){ a+=1; a }`: VC checks r==a_final
            // = 11==11 PROVED, true r==a_entry = 11==10 FALSE). Fail-close: emit ONE not-proved
            // Postcondition VC (a SATisfiable `Bool(true)` is never UNSAT, so it is reported
            // not-proved, NEVER PROVED) until entry-snapshot modeling lands. (FULL is already sound.)
            if prep.refs_mutated_param {
                // Emit `Not(post)` with NO body/param bindings: the parameter is then FREE (its
                // unknown entry value), so the negated postcondition is trivially SATisfiable —
                // reported not-proved (fast, like any refuted postcondition), never PROVED. This
                // routes/reports identically to an ordinary unprovable postcondition (avoids the
                // trust-wp timeout that a bare `Bool(true)` incurs).
                //
                // A Machine{w}-admitted clause MUST take the declared-width BV
                // spelling here too: its `Int` spelling can be an `Int`
                // TAUTOLOGY (`result + 1 > result`), whose bare negation is
                // UNSAT — a FALSE PROOF minted by this very shortcut. The BV
                // reading keeps the wrap witness satisfiable. An untranslatable
                // clause keeps the visible fail-closed row.
                let formula = if *machine_lane {
                    match contracts::machine_faithful_vc_formula(
                        func,
                        &Formula::Not(Box::new(prep.raw_post.clone())),
                    ) {
                        Some(machine) => machine,
                        None => {
                            vcs.push(contracts::spec_unverifiable_vc(
                                func,
                                func.span.clone(),
                                "machine-arithmetic ensures over a reassigned parameter is outside the declared-width fragment",
                                &format!("{:?}", prep.raw_post),
                                clause_metadata,
                            ));
                            continue;
                        }
                    }
                } else {
                    Formula::Not(Box::new(prep.raw_post.clone()))
                };
                vcs.push(VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: fn_sym,
                    location: func.span.clone(),
                    formula,
                    contract_metadata: clause_metadata,
                    obligation: None,
                });
                continue;
            }
            let guard_paths_map = guard_paths_map_cell.get_or_init(|| super::guard_map_for(func));
            let sv = sv_cell.get_or_init(|| super::stmt_versions_for(func));
            let path_definition_map =
                path_definition_map_cell.get_or_init(|| super::path_definition_map_for(func));
            let semantic_guards =
                semantic_guards_cell.get_or_init(|| super::semantic_guard_map_for(func, summaries));
            let out_param_store_sorts =
                out_param_store_sorts_cell.get_or_init(|| out_param_store_sorts(func));
            let dropped_requires =
                dropped_requires_cell.get_or_init(|| dropped_requires_clauses(func));
            let agg_operands = agg_operands_cell.get_or_init(|| {
                vc_blocks
                    .iter()
                    .any(|vb| vb.id != block.id)
                    .then(|| return_slot_aggregate_operand_sorts(func, block))
                    .unwrap_or_default()
            });

            // Re-sort the postcond's return variable `_0` to the real return sort (once per clause).
            let post = prep
                .resorted_post
                .get_or_init(|| substitute_summary_params_owned(prep.raw_post.clone(), &ret_subst));
            let clause_sorts: &FxHashMap<String, Option<Sort>> =
                if out_param_store_sorts.is_empty() && agg_operands.is_empty() {
                    &empty_clause_sorts
                } else {
                    prep.clause_sorts.get_or_init(|| collect_clause_base_sorts(post))
                };
            let base_clause_written_out_params: &[String] = if out_param_store_sorts.is_empty() {
                &[]
            } else {
                prep.base_clause_written_out_params.get_or_init(|| {
                    let mut names: Vec<String> = clause_sorts
                        .keys()
                        .filter(|base| out_param_store_sorts.get(*base).is_some_and(Option::is_some))
                        .cloned()
                        .collect();
                    if names.len() > 1 {
                        names.sort_unstable();
                    }
                    names
                })
            };
            for ((vc_block, metadata_pin), path_cell) in
                vc_blocks.iter().zip(&metadata_pins).zip(&prepared_paths)
            {
                let Some(mut formula) = postcondition_at_return_path(
                    func,
                    sv,
                    vc_block,
                    block,
                    Formula::Not(Box::new(post.clone())),
                ) else {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        v2_block_span(func, block),
                        "postcondition result has no established return-path value",
                        &format!("{post:?}"),
                        clause_metadata.clone(),
                    ));
                    continue;
                };
                formula = v2_formula_with_block_defs(func, block, formula);
                if vc_block.id != block.id {
                    formula = v2_formula_with_block_defs(func, vc_block, formula);
                }

                // (The return slot's two names — the postcond/pin `_0` and the
                // block-def alias `__ret` from `place_to_var_name` — are UNIFIED to
                // `_0` by a single rename over the FINAL formula, just before the VC
                // is pushed below. Renaming, rather than conjoining a `_0 == __ret`
                // bridge, is essential: a `Bool = Bool` variable-equality chain
                // (`_0 = __ret ∧ __ret = (x>0) ∧ _0 != (x>0)`) drives the SMT
                // solver to `unknown` [incomplete theory combination], so a
                // bool-valued postcondition's MUTANT would land `unknown` instead
                // of `failed`. Eliminating the redundant variable lets the solver
                // both prove the valid case and REFUTE the mutant.)

                // Explicitly pin the RETURN VALUE to its definition. The
                // postcondition reasons about `_0`, but block-def extraction does
                // not surface a `_0 = Use(...)` whose source is a CheckedBinaryOp
                // result field (e.g. `_0 = move (_t.0)`), so `_0` stays havoc'd and
                // a valid postcondition is vacuously refutable (cex `_0 = 0` even
                // though `_t.0 = x + 1`). Conjoin `_0 == <expr>` for the return
                // assignment in this block or its predecessor; combined with the
                // assert-passed `_t.0 == x + 1` semantic this pins `_0` to the
                // body's computed result. Sound: `_0` is the return slot, assigned
                // once before `Return`, so the equality holds on the return path.
                let path_prep = path_cell.get_or_init(|| {
                    let vc_block_span = v2_block_span(func, vc_block);
                    let mut direct_return_pins: Vec<Formula> = Vec::new();
                    let mut unlowerable_return_assignment = false;
                    for def_block in [&**vc_block, block] {
                        // Trust (2026-09-30, P2): `k` stamps each pin at its OWN statement.
                        for (k, stmt) in def_block.stmts.iter().enumerate() {
                            let Statement::Assign { place, rvalue, .. } = stmt else {
                                continue;
                            };
                            if place.local != 0 || !place.projections.is_empty() {
                                continue;
                            }
                            // Review round 43: the pin is conjoined BARE, and the final
                            // rename stamps each of its reads with the version at the
                            // return point. A read the path rewrites after this statement
                            // (`let e = y; y = 5; e`, MIR `_0 = copy y; y = 5`) became a
                            // claim about the NEW value: `ensures result == 5` was proved
                            // and kernel-certified while `e` returns the old `y`. Such a
                            // pin is withheld.
                            let path_buf = [(def_block, k + 1), (block, 0)];
                            let path: &[(&trust_types::BasicBlock, usize)] =
                                if std::ptr::eq(def_block, *vc_block) && vc_block.id != block.id {
                                    &path_buf[..]
                                } else {
                                    &path_buf[..1]
                                };
                            // A withheld pin leaves the slot to the other return pins
                            // (the per-path hop below); a slot nothing pins is free, so
                            // its row can fail or be unknown but never prove.
                            let window_buf = [&**vc_block, block];
                            let window: &[&trust_types::BasicBlock] = if vc_block.id == block.id {
                                &window_buf[1..]
                            } else {
                                &window_buf[..]
                            };
                            if !return_pin_reads_are_current(func, path, window, rvalue) {
                                // An operand the encoder cannot lower keeps its old
                                // meaning: the slot is reported unlowerable, so a
                                // partial pin never makes the rest refutable.
                                if rvalue_has_unlowerable_operand(rvalue) {
                                    unlowerable_return_assignment = true;
                                }
                                continue;
                            }
                            // CheckedBinaryOp's value is its `.0` field, pinned via the
                            // assert-passed semantic guard (`_t.0 == x + 1`), NOT its raw
                            // wrapping result — leave it to that path.
                            if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
                                continue;
                            }
                            // Pin `_0 == <rvalue>` for ANY directly-representable return
                            // assignment (Use / BinaryOp / UnaryOp / Cast), not just
                            // `Use`. The block-def relevance filter DROPS a
                            // `__ret == <rvalue>` def when the postcondition shares no
                            // variable with it — e.g. `ensures(r < 0)` for `-x`
                            // references only `_0`, not `x`, so `__ret == Neg(x)` is
                            // pruned and `_0` stays havoc'd, FALSE-REFUTING a valid
                            // postcondition. Pinning by the STANDARD `_0` name the
                            // postcond uses (not the `place_to_var_name` alias `__ret`)
                            // bypasses the relevance filter. Each pin names this
                            // assignment's value, even if a later write replaces it.
                            let return_formula = match (rvalue, metadata_pin) {
                                (
                                    Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, _),
                                    return_metadata::MetadataReturnPin::Exact(length),
                                ) => Ok(length.clone()),
                                _ => crate::chc::rvalue_to_formula(func, rvalue),
                            };
                            // Trust (2026-09-30, P2): stamp the pin's reads at its own
                            // statement; a stamp that cannot be made fails the row
                            // closed exactly like an unlowerable rvalue.
                            let return_formula = return_formula.ok().and_then(|rformula| {
                                stamp_return_pin_reads(
                                    sv, func, vc_block, block, def_block, k, rformula,
                                )
                            });
                            match return_formula {
                                Some(rformula) => {
                                    let sort =
                                        crate::place_sort(func, place).unwrap_or(Sort::Int);
                                    // The destination belongs to this write too.
                                    // A later `_0` assignment must not turn an old
                                    // return pin into a contradictory final-value pin.
                                    let ret_var = version_rename_at(
                                        &Formula::var_owned("_0".to_string(), sort),
                                        sv,
                                        func,
                                        def_block.id,
                                        k + 1,
                                    );
                                    direct_return_pins
                                        .push(Formula::Eq(Box::new(ret_var), Box::new(rformula)));
                                }
                                // A return assignment whose rvalue the encoder
                                // cannot lower must not be SILENTLY dropped: with
                                // no pin the return slot is FREE, the negated
                                // clause becomes vacuously satisfiable, and the
                                // row turns into a refutable query about nothing
                                // (the abs `-x` branch spent a day as exactly this
                                // — a spuriously SAT VC whose native refutation
                                // had to be firewalled to Unknown). Record the
                                // gap; the emission check below fails the row
                                // closed to a VISIBLE unsupported shape when no
                                // other conjunct pinned the slot.
                                None => unlowerable_return_assignment = true,
                            }

                            // Trust (tuple/struct return-aggregate pin, over-refutation
                            // audit #2): a `_0 = (op0, op1, ...)` Tuple / single-variant
                            // struct aggregate return is NOT scalar, so `rvalue_to_formula`
                            // above yields nothing and the return FIELDS `_0.i` stay free.
                            // A postcondition over `ret.0`/`ret.1` (`Var("_0.0")`,
                            // `Var("_0.1")` from the contract parser) is then vacuously
                            // refutable even when the body makes it hold (`(x, x)` ⇒
                            // `_0.0 == _0.1`). Decompose the aggregate: pin each
                            // `_0.i == <field op_i>` under the SAME `_0.i` name the parser
                            // mints (`place_to_var_name` of a `Field(i)` projection).
                            // SOUND: `_0` is assigned once before `Return`, so each field
                            // equality holds on the return path; a FALSE postcondition
                            // stays refutable (each field is pinned to its genuine value,
                            // never credited). Only `Tuple` / variant-0 `Adt` (structs and
                            // single-variant enums) decompose positionally to `.i`;
                            // multi-variant / array / closure aggregates are left free
                            // (fail-closed).
                            if let Rvalue::Aggregate(kind, ops) = rvalue {
                                let positional = matches!(
                                    kind,
                                    AggregateKind::Tuple | AggregateKind::Adt { variant: 0, .. }
                                );
                                if positional {
                                    for (i, op) in ops.iter().enumerate() {
                                        let field_place = Place {
                                            local: place.local,
                                            projections: vec![trust_types::Projection::Field(i)],
                                        };
                                        // Trust (2026-09-30, P2): stamped at the
                                        // aggregate's own statement; unstampable → no pin.
                                        if let Ok(field_formula) =
                                            crate::chc::operand_to_formula_checked(func, op)
                                            && let Some(field_formula) = stamp_return_pin_reads(
                                                sv,
                                                func,
                                                vc_block,
                                                block,
                                                def_block,
                                                k,
                                                field_formula,
                                            )
                                        {
                                            // Pin under the RAW `_<local>.<i>` name the
                                            // contract parser mints (`Var("_0.0")`), NOT
                                            // the `place_to_var_name` alias `__ret.<i>`
                                            // (local 0 carries source name `__ret`) — just
                                            // as the scalar pin above uses raw `_<local>`.
                                            // Otherwise the pin and the postcondition name
                                            // distinct field vars and never connect.
                                            let field_name = format!("_{}.{}", place.local, i);
                                            let field_sort =
                                                crate::place_sort(func, &field_place)
                                                    .unwrap_or(Sort::Int);
                                            direct_return_pins.push(Formula::Eq(
                                                Box::new(Formula::var_owned(
                                                    field_name, field_sort,
                                                )),
                                                Box::new(field_formula),
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Trust (Option/Result-return discriminant/value pin): ground the
                    // synthetic spec-model terms `_0__discr` / `_0__value` that the
                    // contract parser mints for `result.is_none()`/`is_some()`/
                    // `is_ok()`/`is_err()`/`unwrap()` to the body's ACTUAL in-body
                    // `_0 = Some(x)` / `_0 = None` / `_0 = Ok(x)` / `_0 = Err(e)`
                    // construction. Without this the postcondition's wrapper accessors
                    // stay free and a valid `r.is_none() || low <= r.unwrap() <= high`
                    // is un-groundable (the split above routes it to fail-closed
                    // Unknown UNLESS `enum_return_grounded_model_vars` credited it —
                    // which it does ONLY when EVERY return path pins the terms here).
                    // Scoped to the EXACT std/core `Option`/`Result` ADTs. The pinned
                    // value is the PARSER-CONVENTION model discriminant
                    // (`std_enum_model_discr`), NOT the raw machine variant index:
                    // Option's variant order matches the convention (None=0, Some=1 —
                    // identity), while Result's is INVERTED (`Ok` is machine variant 0
                    // but must pin `_0__discr==1`, the parser's `is_ok ⟹ _0__discr!=0`;
                    // `Err` is variant 1 and pins `_0__discr==0`). Pinning the raw
                    // index for Result would swap `is_ok`/`is_err` polarity — a
                    // simultaneous false-PROVE and false-FAIL. Pin at MOST ONE
                    // discriminant per return path (last / nearest-to-return wins) so
                    // two differing-variant assignments can never conjoin
                    // `_0__discr==0 ∧ _0__discr==1` into a vacuous UNSAT (a
                    // false-PROVE). SOUND: `_0 = Some(x)` / `_0 = Ok(x)` literally
                    // carries its variant and payload x, so `_0__discr==<model> ∧
                    // _0__value==x` are exact identities of the constructed value under
                    // the parser's reading; `_0 = None` / `_0 = Err(e)` is
                    // `_0__discr==0` exactly — a FALSE postcondition still refutes
                    // (every term pinned to its genuine value, never credited).
                    // `_0__value` is pinned only on the payload variant's path
                    // (`Some`/`Ok`) with an integer payload; leaving it free on the
                    // other path — and on non-integer payloads (ny-cert's Rat/Vec
                    // shapes, whose `_0__value*` terms the gate keeps UNGROUNDED so
                    // they never reach this refutable lane) — is sound (a free var
                    // only adds SAT/refute, never manufactures UNSAT/proof).
                    let mut enum_return_pins: Vec<Formula> = Vec::new();
                    let enum_return_pin = may_have_enum_return
                        .then(|| {
                            super::witness_grounding::resolve_enum_return_aggregate_located(
                                func, vc_block, block,
                            )
                        })
                        .flatten()
                        .map(|(kind, variant, ops, agg_block, agg_stmt)| {
                            // Parser-convention model discriminant (Result INVERTED).
                            let discr = std_enum_model_discr(kind, variant);
                            let payload = if variant == std_enum_payload_variant(kind)
                                && ops.len() == 1
                                && crate::operand_ty_cow(func, &ops[0])
                                    .as_deref()
                                    .is_some_and(|t| matches!(t, Ty::Int { .. }))
                            {
                                // Trust (2026-09-30, P2): stamp the payload's reads at the
                                // aggregate's OWN statement; no located statement or an
                                // unstampable read drops the payload pin (fail closed).
                                let agg_def_block = func
                                    .body
                                    .blocks
                                    .get(agg_block.0)
                                    .filter(|b| b.id == agg_block);
                                crate::chc::operand_to_formula_checked(func, &ops[0])
                                    .ok()
                                    .and_then(|pf| {
                                        stamp_return_pin_reads(
                                            sv,
                                            func,
                                            vc_block,
                                            block,
                                            agg_def_block?,
                                            agg_stmt?,
                                            pf,
                                        )
                                    })
                            } else {
                                None
                            };
                            (discr, payload)
                        });
                    if let Some((discr, payload)) = enum_return_pin {
                        enum_return_pins.push(Formula::Eq(
                            Box::new(Formula::var_owned("_0__discr".to_string(), Sort::Int)),
                            Box::new(Formula::Int(discr)),
                        ));
                        if let Some(pf) = payload {
                            enum_return_pins.push(Formula::Eq(
                                Box::new(Formula::var_owned("_0__value".to_string(), Sort::Int)),
                                Box::new(pf),
                            ));
                        }
                    }

                    // Trust (len-witness pin, b62): ground the CREDITED payload-
                    // component length pairs (`_0__value.<i>.<j>_len` — the lowered
                    // crown `matches!(r, Ok(c) if c.….len() != c.….len())` idiom) on
                    // this return path, via the SAME per-path resolver the gate ran
                    // (`len_witness_path_pins` — gate/pin agreement is what keeps a
                    // credited term from ever reaching a refutable VC unpinned).
                    // Payload-variant paths conjoin the construction-derived
                    // equality `len_a == len_b` (plus, for the guard shape, the
                    // individual `Vec::len`-dest witness pins); empty-variant paths
                    // conjoin nothing (the terms have no denotation there — free is
                    // the sound direction, and the discr pin already decides those
                    // VCs). Every fact is TRUE of the returned value on this path
                    // (see the len-witness section banner), so a FALSE postcondition
                    // stays refutable.
                    let mut witness_pins: Vec<Formula> = Vec::new();
                    for pair in &len_pairs {
                        if let Some(pins) = len_witness_path_pins(func, *vc_block, block, pair) {
                            witness_pins.extend(pins);
                        }
                    }
                    // Trust (ordering-witness pin, b62 F4): ground the
                    // CREDITED `__trust_ok` pair terms (the sign term is no longer
                    // credited, ORD-WITNESS-CONSISTENT-1; the shapes were
                    // lowered ny selfcheck/branch `matches!(r, Ok((d, c)) if
                    // d > c)` / `Ok(c) if c.is_positive()` idioms over opaque
                    // `Rat` arena handles) on this return path, via the SAME
                    // per-path resolver the gate ran (`ordering_witness_path_pins`
                    // — gate/pin agreement keeps a credited term from ever
                    // reaching a refutable VC unpinned). Payload-variant paths
                    // conjoin ONE guard-derived ordering fact per item (bound to
                    // the dominating witness call's bool edge — never a
                    // re-encoding of the handle ints); empty-variant paths
                    // conjoin nothing (the terms have no denotation there — free
                    // is the sound direction, and the discr pin already decides
                    // those VCs). Every fact is TRUE of the returned values on
                    // this path (see the F4 section banner), so a FALSE
                    // postcondition stays refutable.
                    for item in &ord_items {
                        if let Some(pins) =
                            ordering_witness_path_pins(func, *vc_block, block, item)
                        {
                            witness_pins.extend(pins);
                        }
                    }

                    // Trust (saturating-return pin, over-refutation audit #5): when a
                    // predecessor's TERMINATOR is a std `saturating_add`/`saturating_sub`
                    // call whose dest IS the return slot `_0` (the function returns the
                    // saturating result directly), the general call-dest fact names it via
                    // the `place_to_var_name` alias `__ret`, which does NOT reach the
                    // postcondition's `_0` in this lane. Pin `_0 == clamp(x±y, MIN, MAX)`
                    // under the RAW `_0` name the postcondition uses (exactly as the
                    // scalar/tuple return-pins above do), so `#[ensures(|r| *r >= x)]` over
                    // `x.saturating_add(y)` proves. SOUND: the value is the exact, total std
                    // semantics (see `saturating_call_dest_value`); `_0` is assigned once
                    // before `Return` on this path.
                    let mut call_dest_return_pins: Vec<Formula> = Vec::new();
                    let has_ret_call = [&**vc_block, block].into_iter().any(|tb| {
                        matches!(
                            &tb.terminator,
                            Terminator::Call { dest, .. }
                                if dest.local == 0 && dest.projections.is_empty()
                        )
                    });
                    if has_ret_call {
                        for term_block in [&**vc_block, block] {
                            let Terminator::Call { dest, .. } = &term_block.terminator else {
                                continue;
                            };
                            if dest.local != 0 || !dest.projections.is_empty() {
                                continue;
                            }
                            // Any exact-value MODELED call (saturating_add/sub, wrapping_neg)
                            // whose dest is the return slot. Its value is an `Ite`; a term-
                            // `Ite` in a postcondition obligation is pruned by trust-mc / not
                            // routed by trust-wp, so `_0 == <Ite>` stays UNKNOWN. `ite_free_equality`
                            // LIFTS the `Ite` to formula-level guards, which both backends
                            // discharge — so `#[ensures]` over `x.saturating_add(y)` /
                            // `x.wrapping_neg()` proves. See `ite_free_equality`.
                            let modeled = saturating_call_dest_value(func, &term_block.terminator)
                                .or_else(|| {
                                    wrapping_neg_call_dest_value(func, &term_block.terminator)
                                });
                            if let Some((modeled_dest, value)) = modeled
                                && modeled_dest.local == 0
                                && modeled_dest.projections.is_empty()
                            {
                                call_dest_return_pins.push(ite_free_equality(
                                    &Formula::var_owned("_0".to_string(), ret_sort.clone()),
                                    &value,
                                ));
                            }
                            // Unsigned `div_ceil` returned directly: the same raw-`_0` pin, by
                            // the ceiling's exact linear characterization (no term `Ite`, so
                            // no lift) — see `div_ceil_call_dest_fact`.
                            if let Some((ceil_dest, a, b)) =
                                div_ceil_call_operands(func, &term_block.terminator)
                                && ceil_dest.local == 0
                                && ceil_dest.projections.is_empty()
                            {
                                call_dest_return_pins.push(
                                    super::call_facts::div_ceil_fact_from_operands(
                                        &Formula::var_owned("_0".to_string(), Sort::Int),
                                        a,
                                        b,
                                    ),
                                );
                            }
                        }
                        // Trust (std-intrinsics lane): the SAME return-slot problem for a
                        // function whose tail is a body-less rustc bit intrinsic —
                        // `fn f(x: u32) -> u32 ensures result <= 32 { ctpop(x) }`. The
                        // guard-map fact names the dest `__ret`, which never reaches the
                        // postcondition's `_0`, so the `#[ensures]` read an unconstrained
                        // havoc and the clause was REFUTED. Re-emit the intrinsic's facts
                        // under the RAW `_0` name, exactly as the saturating pin above does.
                        //
                        // No `ite_free_equality` lift is needed: unlike the saturating and
                        // `wrapping_neg` models, none of these definitions contains a term
                        // `Ite` (`ctpop`/`bswap`/`bitreverse` are pure bitvector terms and
                        // the `ctlz`/`cttz` facts are formula-level `Implies` already).
                        //
                        // SOUND: every fact is true of the intrinsic's result for EVERY
                        // input — `intrinsic_semantics` states them and its tests check
                        // each exhaustively at width 8 against the real Rust operation —
                        // and the builder itself requires `_0` to be single-static-assignment
                        // and the argument to be a stable whole local.
                        for term_block in [&**vc_block, block] {
                            if let Terminator::Call { func: callee, dest, .. } =
                                &term_block.terminator
                                && dest.local == 0
                                && dest.projections.is_empty()
                                && callee.starts_with('@')
                            {
                                let ret_var =
                                    Formula::var_owned("_0".to_string(), ret_sort.clone());
                                if let Some((_, facts)) = value_modeled_intrinsic_facts(
                                    func,
                                    &term_block.terminator,
                                    &ret_var,
                                ) {
                                    call_dest_return_pins.extend(facts);
                                }
                            }
                        }
                        // Trust (clamp/min/max return pin, over-refutation audit #8): when a
                        // predecessor's TERMINATOR is an integer std `Ord::min`/`max`/`clamp`
                        // call (a primitive integer `Self`: `primitive_int_ord_method`,
                        // NAME-ANCHOR-2) whose dest IS the return slot `_0` (the function returns the
                        // ordered result directly, e.g. `range_usize`'s
                        // `…unwrap_or(lo).clamp(lo, hi)`), the general call-dest fact
                        // (`build_semantic_guard_map`) names it via the `place_to_var_name`
                        // alias `__ret`, which does NOT reach the postcondition's `_0` in this
                        // lane — `normalize_ssa_version_tokens` collapses `__ret#tok` to the
                        // debug base `__ret`, never `_0`, so a valid `#[ensures(|r| lo<=*r<=hi)]`
                        // over a clamp result was FALSELY REFUTED (the `¬(lo<=_0<=hi)` obligation
                        // stayed havoc'd). This is IDENTICAL to the saturating/wrapping_neg pins
                        // above; re-emit the SAME (sound) result bound under the RAW `_0` name.
                        // SOUND: reuses `ord_min_max_clamp_result_facts` (unconditional min/max
                        // bounds; GUARDED clamp bound `(lo<=hi) -> lo<=_0<=hi`, vacuous when
                        // `lo>hi` so a clamp that PANICS is never false-proved); `_0` is
                        // single-static-assignment (assigned once by this call before `Return`),
                        // the SAME SSA gate the call-dest arm applies.
                        for term_block in [&**vc_block, block] {
                            if let Terminator::Call {
                                func: callee,
                                args,
                                dest,
                                target: Some(_),
                                ..
                            } = &term_block.terminator
                                && dest.local == 0
                                && dest.projections.is_empty()
                                && matches!(method_tail(callee), "min" | "max" | "clamp")
                                && is_single_static_assignment(func, dest.local)
                            {
                                let ret_var =
                                    Formula::var_owned("_0".to_string(), ret_sort.clone());
                                call_dest_return_pins.extend(ord_min_max_clamp_result_facts(
                                    func, callee, args, dest, &ret_var,
                                ));
                            }
                        }
                    }

                    // Trust (branchy computed-return fix, 2026-07-04): the pin above
                    // connects `_0` only to a DIRECT `_0 = <rvalue>`. But a MULTI-RETURN
                    // body routes the value through a shared return binding `__ret`
                    // (`_L`): the return block does `_0 = copy _L`, while each ARM
                    // assigns `_L` (`_L = move _5.0` — a CheckedAdd `.0` field — on the
                    // computed arm, `_L = copy _1` on the plain arm). `_L`/`__ret` is
                    // MULTI-ASSIGNED, so it is NOT single-static-assignment: its per-arm
                    // version tokens do not unify and `normalize_ssa_version_tokens`
                    // cannot collapse them, so the computed arm's value never reaches
                    // `_0` and a VALID branchy postcondition (`if a<100 {a+1} else {a}`
                    // `ensures r>=a`) is falsely refuted. Add ONE transitive hop: when
                    // the return block copies `_0 = _L` (whole-local, L!=0), pin
                    // `_0 == <_L's rvalue on THIS path>` using `_L`'s assignment in the
                    // vc_block arm (else the return block). Combined with the arm's
                    // assert-passed semantic guard (`_5.0 == a+1`) this pins `_0` to the
                    // computed value. SOUND + monotone: `_0 = _L` and `_L = <rvalue>`
                    // both hold on this per-predecessor path (path-consistent copies),
                    // and `_L`'s def is taken ONLY from this arm — so it constrains `_0`
                    // to its genuine per-path value (removes a spurious free-`_0` cex),
                    // never crediting a violated postcondition. CheckedBinaryOp itself
                    // is skipped (its `.0` field is the value, pinned by the semantic
                    // guard); a field-projected Use of it is what we pin here.
                    // The `_0 = copy _L` copy may live in the RETURN block (the
                    // `if a<100 {a+1} else {a}` expression-branch shape) OR in the ARM
                    // itself (the `if x>0 { return 1 }` early-`return` / match-arm
                    // multi-EXIT shape — the Return block is empty and each exit site
                    // does `_L = <val>; _0 = copy _L` in its own block, with distinct
                    // `__ret` temps that ALIAS on the debug name and fall back to RAW
                    // `_L` names, and `_0` is MULTI-assigned so it never normalizes to
                    // bare). Scan BOTH blocks for the copy and for `_L`'s per-path
                    // value, and pin BOTH spellings:
                    //   `_0 == value` — connects when `_0` is SSA and normalizes bare
                    //                   (expression-branch shape);
                    //   `_L == value` — connects when the VC references the RAW temp
                    //                   `_L` (aliased/multi-exit shape) via the
                    //                   already-present `_0#v = _L` block-def.
                    // Both are monotone-sound: `_0 = _L` and `_L = <val>` both hold on
                    // THIS per-predecessor path (path-consistent copies), and `_L`'s def
                    // is taken ONLY from this arm — constraining the return slot to its
                    // genuine per-path value, never crediting a violated postcondition.
                    let scan_blocks: [&trust_types::BasicBlock; 2] = [&**vc_block, block];
                    // Trust (2026-09-30, P4 — hunter Finding 1): carry the COPY's own
                    // location `(copy_block, copy_idx)` out of the search, so `_L`'s
                    // definition can be required to REACH it (below).
                    let return_copy: Option<(&trust_types::BasicBlock, usize, usize)> =
                        scan_blocks
                            .iter()
                            .flat_map(|b| {
                                b.stmts
                                    .iter()
                                    .enumerate()
                                    .rev()
                                    .map(move |(i, s)| (*b, i, s))
                            })
                            .find_map(|(copy_block, copy_idx, stmt)| {
                                let Statement::Assign { place, rvalue, .. } = stmt else {
                                    return None;
                                };
                                if place.local != 0 || !place.projections.is_empty() {
                                    return None;
                                }
                                match rvalue {
                                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                        if p.projections.is_empty() && p.local != 0 =>
                                    {
                                        Some((copy_block, copy_idx, p.local))
                                    }
                                    _ => None,
                                }
                            });
                    let arm_copy_pin = if let Some((copy_block, copy_idx, src)) = return_copy {
                        // Trust (2026-09-30, P2): carry the defining `(block, k)` out so
                        // the pins are stamped at `_L`'s OWN statement.
                        //
                        // Trust (2026-09-30, P4 — hunter Finding 1): the definition must
                        // be the one that REACHES `_0 = copy _L`. The scan used to run
                        // the PREDECESSOR's statements first and each block backwards
                        // from its END, taking the first `_L = ..` it met — so it could
                        // pick a write AFTER the copy (`_3 = copy (*_1); _0 = copy _3;
                        // _3 = copy _2`: `replace(slot, v) ensures result == v` proved
                        // although it returns the OLD value) or the predecessor's write
                        // when the Return block rewrites `_L` before the copy
                        // (`let mut r = a; extr(&r); r = !r; r` proved
                        // `ensures result && !result`). Both were measured false proofs
                        // through the falsification gate's flags. Now the search walks
                        // BACKWARDS FROM THE COPY — the copy block's statements before
                        // `copy_idx`, then (only when the copy is in the Return block and
                        // the predecessor is a separate block) the predecessor's — and
                        // the candidate must pass the SAME oracle that renamed the VC:
                        //   * same block: `version_token_at(copy_block, copy_idx, _L)`
                        //     is exactly the def's own write token `s{b}_{k}`;
                        //   * predecessor def, Return-block copy: the def's token is the
                        //     one at the predecessor's END, the predecessor's terminator
                        //     does not rebind `_L` (a call destination writes after the
                        //     statements), and the Return block does not write `_L`
                        //     before the copy (its token there equals its entry token).
                        // Anything else drops BOTH `pin_ret` and `pin_src` (fail closed).
                        let def_is_src = |stmt: &Statement| {
                            matches!(stmt, Statement::Assign { place, .. }
                                if place.local == src && place.projections.is_empty())
                        };
                        let in_copy_block = copy_block.stmts[..copy_idx]
                            .iter()
                            .enumerate()
                            .rev()
                            .find(|(_, stmt)| def_is_src(stmt))
                            .map(|(k, stmt)| (copy_block, k, stmt));
                        let from_pred = copy_block.id == block.id && vc_block.id != block.id;
                        let candidate = match in_copy_block {
                            Some(found) => Some(found),
                            None if from_pred => vc_block
                                .stmts
                                .iter()
                                .enumerate()
                                .rev()
                                .find(|(_, stmt)| def_is_src(stmt))
                                .map(|(k, stmt)| (&**vc_block, k, stmt)),
                            None => None,
                        };
                        let def_reaches_copy = |def_block: &trust_types::BasicBlock, k: usize| {
                            let src_var = crate::place_to_var_name(func, &Place::local(src));
                            let def_tok = format!("s{}_{k}", def_block.id.0);
                            if def_block.id == copy_block.id {
                                return k < copy_idx
                                    && sv
                                        .version_token_at(func, copy_block.id, copy_idx, &src_var)
                                        .as_deref()
                                        == Some(def_tok.as_str());
                            }
                            from_pred
                                && def_block.id == vc_block.id
                                && sv
                                    .version_token_at(
                                        func,
                                        vc_block.id,
                                        vc_block.stmts.len(),
                                        &src_var,
                                    )
                                    .as_deref()
                                    == Some(def_tok.as_str())
                                && sv.terminator_kill(func, vc_block).survives(&Formula::var_owned(
                                    src_var.clone(),
                                    crate::place_sort(func, &Place::local(src))
                                        .unwrap_or(Sort::Int),
                                ))
                                && sv.version_token_at(func, block.id, copy_idx, &src_var)
                                    == sv.version_token_at(func, block.id, 0, &src_var)
                        };
                        // Review round 43 (local twin of P4, kept on merge 2026-10-14 so the
                        // pin is admitted only when BOTH gates admit it): nothing may write
                        // `_L` after its def anywhere in the window (statements or
                        // terminators), `_L` must not escape, and the def's own reads must
                        // still be current at the return point.
                        let own_scan_blocks_buf = [&**vc_block, block];
                        let own_scan_blocks: &[&trust_types::BasicBlock] =
                            if vc_block.id == block.id {
                                &own_scan_blocks_buf[1..]
                            } else {
                                &own_scan_blocks_buf[..]
                            };
                        let local_order_admits =
                            |def_block: &trust_types::BasicBlock, k: usize, rvalue: &Rvalue| {
                                let Some(def_bi) =
                                    own_scan_blocks.iter().position(|b| b.id == def_block.id)
                                else {
                                    return false;
                                };
                                let writes = |stmt: &Statement| {
                                    !matches!(
                                        stmt.local_write(src),
                                        trust_types::LocalWrite::Untouched
                                    )
                                };
                                let later_stmt_write = own_scan_blocks
                                    .iter()
                                    .enumerate()
                                    .skip(def_bi)
                                    .any(|(bi, b)| {
                                        let from = if bi == def_bi { k + 1 } else { 0 };
                                        b.stmts
                                            .get(from..)
                                            .is_some_and(|rest| rest.iter().any(writes))
                                    });
                                let later_terminator_write =
                                    own_scan_blocks.iter().skip(def_bi).any(|b| {
                                        !matches!(
                                            b.terminator.local_write(src),
                                            trust_types::LocalWrite::Untouched
                                        )
                                    });
                                if later_stmt_write
                                    || later_terminator_write
                                    || crate::any_local_write_stmt(
                                        func,
                                        &func.body.blocks,
                                        src,
                                        |_block, stmt| crate::stmt_escapes_local(func, stmt, src),
                                    )
                                {
                                    return false;
                                }
                                let def_path_buf = [(own_scan_blocks[def_bi], k + 1), (block, 0)];
                                let def_path = &def_path_buf[..own_scan_blocks.len() - def_bi];
                                return_pin_reads_are_current(func, def_path, own_scan_blocks, rvalue)
                            };
                        let arm_def = candidate
                            .filter(|(def_block, k, _)| def_reaches_copy(def_block, *k))
                            .filter(|(def_block, k, stmt)| match stmt {
                                Statement::Assign { rvalue, .. } => {
                                    local_order_admits(def_block, *k, rvalue)
                                }
                                _ => false,
                            })
                            .and_then(|(def_block, k, stmt)| {
                                let Statement::Assign { rvalue, .. } = stmt else {
                                    return None;
                                };
                                if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
                                    return None;
                                }
                                crate::chc::rvalue_to_formula(func, rvalue)
                                    .ok()
                                    .map(|rformula| (def_block, k, rformula))
                            });
                        // `rformula_for_scope` stays RAW: the scope gate below parses raw
                        // `_N` names. The pinned copy is stamped at `(def_block, k)`, and
                        // the source local `_L` it defines at `k + 1` (the value just
                        // after its write — never a later reseat's or the predecessor's
                        // spelling; bare only when NO point versions the raw name, so
                        // no rename can re-stamp it). A read stamp failing drops both
                        // pins; a source spelling that cannot be fixed drops `pin_src`
                        // alone (fail closed).
                        let arm_def = arm_def.and_then(|(def_block, k, rformula)| {
                            let stamped = stamp_return_pin_reads(
                                sv,
                                func,
                                vc_block,
                                block,
                                def_block,
                                k,
                                rformula.clone(),
                            )?;
                            let src_name = format!("_{src}");
                            let src_lhs =
                                match sv.version_token_at(func, def_block.id, k + 1, &src_name) {
                                    Some(tok) => Some(format!("{src_name}#{tok}")),
                                    None if !sv.ever_versioned(func, &src_name) => Some(src_name),
                                    None => None,
                                };
                            Some((rformula, stamped, src_lhs))
                        });
                        if let Some((rformula_for_scope, rformula, src_lhs)) = arm_def {
                            let pin_ret = Formula::Eq(
                                Box::new(Formula::var_owned("_0".to_string(), ret_sort.clone())),
                                Box::new(rformula.clone()),
                            );
                            // Review round 45 (local; composed with upstream's P2 stamping on
                            // merge 2026-10-14): a BARE `_L` name is the one the
                            // predecessor's block defs also use for `_L`'s EARLIER value
                            // (`let mut r = x; r = r + 1; r` gave `_2 == _2 + 1`,
                            // unsatisfiable: every clause proved). A bare `pin_src` is stated
                            // only when the def is `_L`'s ONLY write on the path; a
                            // version-stamped `_L#tok` names the def's own value and needs no
                            // such gate. `pin_ret` alone connects `_0` otherwise.
                            let mut pins = vec![pin_ret];
                            if let Some(src_lhs) = src_lhs
                                && (src_lhs.contains('#')
                                    || local_writes_reaching(func, own_scan_blocks, src) == 1)
                            {
                                pins.push(Formula::Eq(
                                    Box::new(Formula::var_owned(src_lhs, ret_sort.clone())),
                                    Box::new(rformula),
                                ));
                            }
                            // Trust (plain-`BinaryOp` return value, 2026-09-17): ONE
                            // MORE HOP, by the audit-#7 route below.
                            //
                            // The pin above binds the return slot to `_L`'s rvalue.
                            // When that rvalue is itself a WHOLE LOCAL this arm
                            // assigns — `_2 = _8` after `_8 = x / 2`, the MIR of
                            // `if x < 0 { 0 } else { x / 2 }` — the pin INTRODUCES
                            // `_8` and nothing grounds it. `_8`'s defining equation
                            // is a BLOCK definition, and `v2_formula_with_block_defs`
                            // already ran its relevance filter against a body whose
                            // only free variables were `_0` and the merged `_2`
                            // token. `_8` was not among them, so `_8 == x / 2` was
                            // pruned BEFORE this pin created the link; the solver
                            // then sees `_8` free and the TRUE postcondition
                            // `result >= 0` is satisfiably negated. Measured: the
                            // row came back `unknown`, and a `_8 = -1` model is a
                            // model of the encoding, never of the program.
                            //
                            // Checked arithmetic never hits this. `a + 1` lowers to
                            // `CheckedBinaryOp`, whose value is a FIELD (`_5.0`)
                            // pinned by the arm's assert-passed semantic guard — a
                            // lane that survives the merge. Division, remainder and
                            // the shifts are plain `BinaryOp`, so their value
                            // equation exists ONLY as a block def. That is why the
                            // defect is operator-shaped rather than general, which
                            // is otherwise a baffling thing for a verifier to be.
                            //
                            // Re-conjoin the block defs now that the name exists,
                            // exactly as the deref-load return fix below does for
                            // its own late-introduced referent. SOUND for the same
                            // reason: block defs are TRUE facts of the body, stamped
                            // at their own establish points, and relevance is a
                            // solver-performance heuristic rather than a soundness
                            // gate — so a FALSE postcondition stays refutable, and
                            // the falsification suite is the standing guard on that.
                            //
                            // SCOPED to the shape that needs it: the pinned rvalue
                            // names a whole local THIS arm assigns. A field operand
                            // (`_5.0`, the checked-arithmetic shape) does not match,
                            // and neither does a parameter read (`_L = copy _1`), so
                            // no other return shape's formula is perturbed.
                            let reconjoin = transitive_pin_names_locally_defined_local(
                                &rformula_for_scope,
                                &scan_blocks,
                            );
                            Some((pins, reconjoin))
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    // Trust (deref-load return over-refutation, audit #7, 2026-07-06):
                    // a return via a `&mut`/`&` store-then-load (`let p=&mut x; *p=v; *p`,
                    // `#[ensures(|r| *r==v)]`) is FALSELY REFUTED. The block-def pass DOES
                    // compute the correct, self-consistent chain `x#<k>==v` (the store) and
                    // `__ret#<k'>==x#<k>` (the load), but `v2_formula_with_block_defs` ran its
                    // relevance filter (`combine_relevant_block_defs`) against the bare
                    // obligation `¬(_0==v)` — whose only free var is `_0` — BEFORE the
                    // return-value pin above reconnected `_0` to the referent `x#<k>`. Both
                    // defs mention `x#<k>`/`__ret#<k'>`, not `_0`, so they were pruned; the
                    // late pin then reintroduced `x#<k>` with no `x#<k>==v` to ground it, so
                    // `¬(_0==v)` stayed SAT. The pins above now put the referent version
                    // (`x#<k>`) back into `formula`, so RE-conjoining the relevant block-defs
                    // pulls the establishing store `x#<k>==v` (and transitively the load def)
                    // back in — and `¬(_0==v)` becomes UNSAT (proved). SOUND: block-defs are
                    // TRUE facts of the body (relevance is a solver-perf heuristic, never a
                    // soundness gate — see `combine_relevant_block_defs`), so a FALSE
                    // postcondition stays refutable (each fact pins a genuine value, never
                    // credits a violation). SCOPED to a whole-return `_0 = copy/move(*p)`
                    // deref-LOAD so no other return shape's formula is perturbed.
                    let returns_via_deref_load = |b: &trust_types::BasicBlock| {
                        b.stmts.iter().any(|stmt| {
                            matches!(stmt, Statement::Assign { place, rvalue, .. }
                                if place.local == 0
                                    && place.projections.is_empty()
                                    && matches!(rvalue,
                                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                            | Rvalue::CopyForDeref(p)
                                        if matches!(p.projections.first(),
                                            Some(trust_types::Projection::Deref))))
                        })
                    };
                    let has_deref_load_return = returns_via_deref_load(block)
                        || (vc_block.id != block.id && returns_via_deref_load(vc_block));

                    let edge_guard = (vc_block.id != block.id)
                        .then(|| return_edge_guard(func, vc_block, block.id))
                        .flatten();

                    let live_path_defs = if let Some(path_defs) = path_definition_map.get(&vc_block.id)
                        && !path_defs.is_empty()
                    {
                        let mut live = v2_live_path_defs(func, vc_block, path_defs);
                        // soundness (round-11): v2_live_path_defs only sees
                        // STATEMENT-level redefs, so a fact the block's TERMINATOR
                        // invalidates (a `Call` dest such as `_0`, or a `&mut`/`&raw
                        // mut` pointee escaping into the call) would survive into the
                        // postcondition VC and vacuously discharge it. Drop those here,
                        // mirroring the fixpoint outflow kill. Monotone-sound.
                        let kill = sv.terminator_kill(func, vc_block);
                        if !kill.is_empty() {
                            live.retain(|f| kill.survives(f));
                        }
                        live
                    } else {
                        Vec::new()
                    };

                    // Conjoin assert-passed semantic guards from BOTH the predecessor
                    // (vc_block) AND the return block itself — EXEMPT from the rename.
                    let mut sem_conjuncts: Vec<Formula> = Vec::new();
                    if let Some(g) = semantic_guards.get(&block.id) {
                        sem_conjuncts.extend(g.iter().cloned());
                    }
                    if vc_block.id != block.id
                        && let Some(g) = semantic_guards.get(&vc_block.id)
                    {
                        sem_conjuncts.extend(g.iter().cloned());
                    }

                    PreparedReturnPath {
                        vc_block_span,
                        direct_return_pins,
                        unlowerable_return_assignment,
                        enum_return_pins,
                        witness_pins,
                        call_dest_return_pins,
                        arm_copy_pin,
                        has_deref_load_return,
                        edge_guard,
                        live_path_defs,
                        sem_conjuncts,
                        unmarked_sysroot_call: std::cell::OnceCell::new(),
                    }
                });

                let unlowerable_return_assignment = path_prep.unlowerable_return_assignment;
                for def in &path_prep.direct_return_pins {
                    formula = Formula::And(vec![def.clone(), formula]);
                }

                // Trust (OUT-PARAMETER pin): a postcondition over a place written
                // THROUGH a `&mut` PARAMETER (`ensures *x == 0`, `ensures self.n
                // == 0`) had NO antecedent at all and was decided by havoc.
                //
                // The block-def extraction DOES produce the fact
                // (`Eq(Var("x*"), Int(0))` for `(*_1) = 0`), but until 2026-09-30
                // `version_block_def_at_establish` could not stamp it: it looked
                // for the establish point of the `*`-STRIPPED base (`x`), and a
                // `&mut` PARAMETER is never assigned in-body, so the fact was left
                // BARE. The obligation body IS versioned (`x*#s0_0`), so the bare
                // fact was name-disjoint and `combine_relevant_block_defs` pruned it
                // as irrelevant; the VC collapsed to a query about a free variable,
                // and TRUE and FALSE twins came back identically Failed. (The same
                // bare fact, threaded into a successor, also conflated the stored
                // value with the value read before the store — a certified false
                // proof; `block_defs::def_subject_establish_stmt` now stamps it.)
                //
                // The pin stays: it carries the liveness gate and the
                // silent-weakening ledger (`unpinned_out_params`), exactly as the
                // return slot above is pinned ("block-def extraction does not
                // surface a `_0 = Use(..)` ... so `_0` stays havoc'd"). Where the
                // stamped def is already a conjunct, the pin repeats it; a repeated
                // conjunct changes no model, and the exact-formula tests
                // (`mut_ref_postcondition_tests`) read the pair as the witness that
                // both lanes bind the store.
                let (with_pins, unpinned_out_params) = if out_param_store_sorts.is_empty() {
                    (formula, Vec::new())
                } else {
                    with_out_param_pins(
                        func,
                        sv,
                        block,
                        &[vc_block, &block],
                        clause_sorts,
                        formula,
                    )
                };
                formula = with_pins;

                for pin in &path_prep.enum_return_pins {
                    formula = Formula::And(vec![pin.clone(), formula]);
                }

                for pin in &path_prep.witness_pins {
                    formula = Formula::And(vec![pin.clone(), formula]);
                }

                for pin in &path_prep.call_dest_return_pins {
                    formula = Formula::And(vec![pin.clone(), formula]);
                }

                if let Some((ref copy_pins, reconjoin_block_defs)) = path_prep.arm_copy_pin {
                    let mut pins = Vec::with_capacity(copy_pins.len() + 1);
                    pins.extend(copy_pins.iter().cloned());
                    pins.push(formula);
                    formula = Formula::And(pins);
                    if reconjoin_block_defs {
                        formula = v2_formula_with_block_defs(func, block, formula);
                        if vc_block.id != block.id {
                            formula = v2_formula_with_block_defs(func, vc_block, formula);
                        }
                    }
                }

                if path_prep.has_deref_load_return {
                    formula = v2_formula_with_block_defs(func, block, formula);
                    if vc_block.id != block.id {
                        formula = v2_formula_with_block_defs(func, vc_block, formula);
                    }
                }

                // Trust (EARLY-RETURN / DIVERGENT-EXIT postcondition
                // false-refutation, 2026-08-02): the RETURN-EDGE GUARD and the
                // MERGE PIN — the two facts a MULTI-PREDECESSOR `Return` block
                // needs and that no existing lane supplies.
                //
                // The obligation body is versioned at the return block's end.
                // With several return predecessors `version_token_at` hands a
                // `&mut`-parameter place the reaching-def JOIN token
                // (`self*.0.0#e_s1_0`), while EVERY conjunct that could
                // constrain it — the out-parameter pin, the block defs, the
                // semantic guards — carries a SINGLE establish token
                // (`self*.0.0#s1_0`) or the bare entry name. The join name is
                // name-disjoint from all of them, so it is FREE, and
                // `Not(post)` is satisfiable BY HAVOC. Confirmed end to end:
                // `ensures !self.st.f` over `if !self.st.f { return; }
                // self.st.f = false;` emitted
                // `(and true (not (not |self*.0.0#e_s1_0|)))` — a query about
                // nothing — and its EXACT NEGATION emitted
                // `(and true (not |self*.0.0#e_s1_0|))`, so `P` and `!P` came
                // back with byte-identical verdicts. A verifier that answers
                // the same for a clause and its negation is not checking that
                // clause at all.
                //
                // Both facts are PER-PREDECESSOR, which is exactly what this
                // VC is: `vc_blocks` is the return block's predecessor list, so
                // this row quantifies over the executions that enter the return
                // block through `vc_block` and no others.
                //
                // Conjoined HERE — after the deref-load re-conjoin above, which
                // renames the whole formula at the RETURN block and would
                // rewrite an entry-valued pin operand into the very join name
                // the pin exists to constrain — and re-run through
                // `v2_formula_with_block_defs` at the PREDECESSOR so the
                // relevance filter can finally keep the defs that mention the
                // names these facts introduce (the `_2 == self*.0.0` tying the
                // guard temp to the flag was previously pruned as irrelevant,
                // because nothing else in the VC mentioned either name). That
                // re-run renames at `(vc_block, vc_block.stmts.len())`, which is
                // the IDENTITY on both facts: the guard is conjoined bare and is
                // MEANT to be stamped at that point, and the pin's predecessor
                // operand is bare exactly when `version_token_at` is `None`
                // there, so it renames to itself.
                if vc_block.id != block.id {
                    let (merge_pins, store_grounds) = return_edge_merge_pins(
                        func,
                        sv,
                        vc_block,
                        block,
                        clause_sorts,
                        out_param_store_sorts,
                        agg_operands,
                    );
                    let mut edge_facts: Vec<Formula> = Vec::new();
                    edge_facts.extend(path_prep.edge_guard.clone());
                    edge_facts.extend(merge_pins);
                    if !edge_facts.is_empty() {
                        edge_facts.push(formula);
                        formula = Formula::And(edge_facts);
                        formula = v2_formula_with_block_defs(func, vc_block, formula);
                    }
                    // The upstream store's own defining equation is already
                    // stamped at ITS establish point, so it is conjoined AFTER
                    // the predecessor-point rename above — re-stamping its
                    // operands at the predecessor would read them at the wrong
                    // program point.
                    if !store_grounds.is_empty() {
                        let mut with_grounds = store_grounds;
                        with_grounds.push(formula);
                        formula = Formula::And(with_grounds);
                    }
                }

                if !path_prep.live_path_defs.is_empty() {
                    let mut conjuncts = Vec::with_capacity(path_prep.live_path_defs.len() + 1);
                    conjuncts.extend(path_prep.live_path_defs.iter().cloned());
                    conjuncts.push(formula);
                    formula = Formula::And(conjuncts);
                }

                // Trust S2c (exemption): path + semantic guards conjoined AFTER the
                // rename (moved below), exempt from it.
                {
                    // Trust: P-B — unconditional rename (see the v2 lane). Required
                    // so an establish-versioned threaded fact connects to its LIVE
                    // postcondition-lane successor read; verdict-preserving with
                    // empty preconditions.
                    let killed = &empty_kill;
                    formula = conjoin_preconditions_versioned(
                        func,
                        vc_block.id,
                        &func.preconditions,
                        killed,
                        formula,
                    );
                }
                // Trust (a7 — ONE POSTCONDITION ROW PER ENUMERATED RETURN PATH,
                // 2026-09-18). MEASURED root cause of two-language battery
                // blocker a7, on managed `trustc d75f13f97`:
                //
                //   `fn pick(a,b) ensures a <= 1000000 ==> result >= a`
                //   `{ if a >= 1000000 { 1000000 } else if b >= a { b } else { a } }`
                //
                // lowers to a Return block with TWO predecessors, one of which is
                // the `goto`-only JOIN of the inner `if`'s two arms. That one
                // predecessor is reached by TWO guard paths, so
                // `v2_formula_with_path_guards` wraps its row as
                // `Or([And([guards_1, body]), And([guards_2, body])])`. Measured
                // verdicts on that toolchain: the FLAT sibling row
                // (`vc:…:postcondition:0`) is proved by `trust-full-verifier` with
                // a trust-mc PDR receipt; the `Or`-shaped row
                // (`vc:…:postcondition:1`) gets no such receipt and falls back to
                // `ay-in-process`, whose authority the source-clause composition
                // rule does not accept — so the clause stays UNDISCHARGED although
                // every body row reads `Proved`.
                //
                // The SAME function written with early `return`s gets one FLAT row
                // per path (rustc gives each `return` its own `Return` block) and
                // measures 4 proved / 0 unknown, marker discharged. The defect is
                // therefore the row SHAPE, not the clause, the arithmetic or the
                // path count: an author who writes the value-producing `if`
                // expression is charged a disjunctive query that the `return`
                // spelling of the same program is not.
                //
                // SPLIT IT. `Or(t_1..t_n)` is UNSAT exactly when every `t_i` is
                // UNSAT, so emitting one row per `t_i` DISTRIBUTES the path-guard
                // conjunct: no fact is added, dropped or changed by the split
                // itself, and the CONJUNCTION of the emitted `t_i` is logically
                // identical to the single `Or` row it replaces. A clause violated
                // on path `i` leaves `t_i` satisfiable and that row fails closed
                // exactly as the merged row did, so nothing false becomes provable
                // (the false twins are the standing guard on that).
                //
                // NOT PURE DISTRIBUTION, AND SAYING SO. The shared tail below is
                // SPINE-sensitive in two places, and a per-path row has a
                // positive `And` spine where the merged `Or` row had none, so a
                // per-path row can be STRICTLY more provable than the corresponding
                // disjunct of the merged row. See `finish_row`'s header for the
                // per-helper argument. The direction is fail-open-to-verdict, never
                // credit-a-violation: each helper is scoped to the return slot and
                // a per-path row is a RESTRICTION of the per-predecessor row those
                // helpers were written for.
                //
                // The per-path inputs are built HERE, from the same
                // `formula`/guard map the merged row is built from, and are then
                // taken through the SAME tail as the merged row (`finish_row`
                // below) — one function, so the emitted rows can never drift from
                // the decisions taken on the merged row.
                //
                // DROPPED-`requires` FUNCTIONS DECLINE THE SPLIT ENTIRELY. Of the
                // four `spec_unverifiable_vc` decisions below, three are shape
                // tests that on an `Or` row are at least as eager as they would be
                // on any one path (`formula_has_return_slot_pin` has no `Or` arm
                // and so reads "unpinned"; `formula_pins_var_name`'s `Or` arm
                // requires EVERY arm to pin), so deciding them on the merged row
                // can only suppress rows a per-path decision would have emitted.
                // The 2026-08-06 dropped-`requires` tripwire is the exception and
                // runs the other way: `only_excluded_counterexamples` is a
                // PER-MODEL test, `models(Or(t_1..t_n))` is the UNION of the
                // `models(t_i)`, so "every model of the merged row is an entry
                // state the dropped `requires` excludes" is STRICTLY STRONGER than
                // the same statement about one `t_i`. Deciding it on the merged row
                // and then shipping per-path rows could therefore emit a row whose
                // own models are all excluded — the false-refutation-against-correct-code
                // this P0 guard exists to stop. Rather than re-run a bounded model
                // search per path (a larger change, and one nothing in this lane
                // measured), a function whose contract preconditions the gate
                // dropped keeps HEAD's single merged row: `dropped_requires` is
                // per-FUNCTION, so this is decided identically for every clause and
                // every predecessor of such a function. The `machine_lane` half
                // mirrors the tripwire's own `!*machine_lane` guard — that lane
                // never consults the model search at all, so splitting there
                // bypasses no decision.
                //
                // An empty vector means "no split": one row, spelled exactly as
                // before.
                let split_declined_for_dropped_requires =
                    !*machine_lane && !dropped_requires.is_empty();
                let path_split_inputs: Vec<Formula> = match guard_paths_map.get(&vc_block.id) {
                    Some(paths)
                        if !split_declined_for_dropped_requires
                            && (2..=POSTCONDITION_PATH_SPLIT_CAP).contains(&paths.len()) =>
                    {
                        paths
                            .iter()
                            .map(|path| {
                                v2_formula_with_path_guards(
                                    func,
                                    sv,
                                    vc_block.id,
                                    std::slice::from_ref(path),
                                    formula.clone(),
                                )
                            })
                            .collect()
                    }
                    _ => Vec::new(),
                };
                if let Some(block_guard_paths) = guard_paths_map.get(&vc_block.id) {
                    formula = v2_formula_with_path_guards(
                        func,
                        sv,
                        vc_block.id,
                        block_guard_paths,
                        formula,
                    );
                }
                // The tail EVERY emitted row of this (clause, predecessor) shares.
                // It is a closure rather than inline code so the per-path rows and
                // the merged row cannot diverge: a row that reached a different
                // normalization than the one the tripwires below judged would be a
                // row nothing had checked.
                //
                // Two of these steps are SPINE-sensitive —
                // `dedup_identical_return_slot_pin` and, in the tripwires,
                // `formula_has_return_slot_pin` walk only
                // the positive `And` spine. On an `Or`-rooted merged row that spine
                // is empty, so they are no-ops; on a per-path row they see the pins
                // this lane conjoined and can fire. That is the intended direction:
                // each helper retains the return slot's versioned value, and a
                // per-path row is a RESTRICTION of the per-predecessor row those helpers were written
                // for — so their soundness arguments hold a fortiori. They can turn
                // a fail-closed non-verdict into a verdict; they cannot credit a
                // violated clause.
                let finish_row = |mut formula: Formula| -> Formula {
                    if !path_prep.sem_conjuncts.is_empty() {
                        let mut sem_conjuncts =
                            Vec::with_capacity(path_prep.sem_conjuncts.len() + 1);
                        sem_conjuncts.extend(path_prep.sem_conjuncts.iter().cloned());
                        sem_conjuncts.push(formula);
                        formula = Formula::And(sem_conjuncts);
                    }

                    // Unify the return slot's two names to `_0`: rename the block-def
                    // alias `__ret` (from `place_to_var_name`) onto the `_0` the
                    // postcond and the `Rvalue::Use` pin use. This connects a non-`Use`
                    // return assignment (e.g. a `BinaryOp` comparison `_0 = (x > 0)`
                    // captured by block-def extraction as `__ret == (x > 0)`) to the
                    // postcondition WITHOUT introducing a `_0 == __ret` Bool-equality
                    // chain that drives the SMT solver to `unknown`. Sound: both names
                    // denote local 0. No-op when the alias is already `_0`.
                    if let Some(subst) = &ret_alias_subst {
                        formula = substitute_summary_params_owned(formula, subst);
                    }

                    // Trust (safe-midpoint postcondition, 2026-07-08): conjoin the
                    // FUNCTION-WIDE invariant facts — the same set the hardened panic
                    // lane and the v2 block-VC lane already conjoin (their per-builder
                    // docs prove each fact unconditionally true and SSA-gated, so
                    // "conjoining the set onto ANY VC of `func` is sound"). Without
                    // them a postcondition consuming a CHECKED-OP RESULT copied out of
                    // its overflow pair (`_dst = (_c.0)`; the classic
                    // `low + (high - low) / 2`) leaves `_dst` COMPLETELY FREE in this
                    // lane: z3 on the emitted VC produced `_dst ≈ 2^127` while the
                    // computed sum was in range — a TRUE postcondition spuriously
                    // refuted. Conjoined BEFORE `normalize_ssa_version_tokens` so the
                    // facts' bare whole-local names unify with the body's versioned
                    // reads (the same collapse argument the safety lane relies on).
                    // Less the element-read congruences it cannot use
                    // (`RowGlobalFacts::for_row`).
                    let global_facts = global_facts_cell
                        .get_or_init(|| build_global_invariant_facts(func))
                        .for_row(&formula);
                    if !global_facts.is_empty() {
                        let mut with_facts = global_facts;
                        with_facts.push(formula);
                        formula = Formula::And(with_facts);
                    }

                    // Collapse only locals that are genuinely single-assignment.
                    // A multiply-written return slot keeps its per-write tokens,
                    // including historical values consumed by path guards.
                    formula = normalize_ssa_version_tokens_owned(func, formula);
                    formula =
                        return_metadata::normalize_stable_length_epochs(formula, metadata_pin);

                    // Block-def extraction and the explicit return-pin fallback can
                    // converge to the SAME `_0 == value` equality only after the
                    // return alias and SSA tokens above are normalized.  Keep one
                    // copy: besides avoiding a redundant solver premise, this keeps
                    // the live postcondition formula byte-equal to the independently
                    // reconstructed trust-ir spine formula.  The helper is narrowly
                    // gated to an AST-identical return-slot equality already present
                    // on the unconditional `And` spine; nonidentical pins and every
                    // other semantic guard are preserved.
                    formula = dedup_identical_return_slot_pin(formula);
                    formula
                };
                formula = finish_row(formula);
                // Per-path rows, through the identical tail.
                let mut path_split_rows: Vec<Formula> =
                    path_split_inputs.into_iter().map(&finish_row).collect();

                // Silent-weakening tripwire: a return assignment failed to
                // lower AND nothing else pinned the return slot AND the
                // negated clause actually constrains it — the assembled VC
                // would be a refutable query over a FREE return value, i.e. a
                // spuriously satisfiable formula about nothing. Emit the
                // VISIBLE fail-closed row instead. (When some other conjunct
                // pinned the slot — the semantic-guard path, block defs after
                // the `__ret` rename — the VC is still meaningful and
                // proceeds; a clause that never references the slot is
                // unaffected by the missing pin.)
                if unlowerable_return_assignment
                    && formula_refs_return_slot
                    && !formula_has_return_slot_pin(&formula)
                    && !formula_has_complete_return_projection_pins(&formula, &post)
                {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        path_prep.vc_block_span.clone(),
                        "return assignment is outside the encoder fragment and no conjunct pins the return slot; refusing a refutable query over a free return value",
                        &format!("{post:?}"),
                        clause_metadata,
                    ));
                    continue;
                }

                // Trust (INTRINSIC-RESIDUAL-1, 2026-10-08) — the CALL twin of the
                // tripwire above. A return slot written directly by a call
                // TERMINATOR has no statement for the pin loop to lower, so it is
                // pinned only by the per-callee models this lane conjoins
                // (saturating ≤ 64 bits, `wrapping_neg`, the bit intrinsics,
                // `Ord::min/max/clamp`). An unmodeled sysroot method
                // (`i32::unsigned_abs`, `u128::saturating_add`) leaves `_0` FREE, and
                // the row is a refutable query over havoc: measured on the stage-2
                // capture `fn f(x: i32) -> u32 ensures result <= 2147483648 {
                // x.unsigned_abs() }` as `Failed { _0 = 2147483649 }` — a value the
                // call never returns — with the formula `range(x) ∧ ¬(_0 ≤ 2147483648)`.
                // Fire only for an unmarked sysroot callee
                // (`return_slot_written_by_unmarked_sysroot_call` says why) and only
                // when NOTHING but the negated clause mentions the return slot
                // (`return_slot_only_in_negated_clause`), so a modeled call, a
                // callee fact or a guard that constrains `_0` keeps its row. Firing
                // can only withhold a verdict: a row that would have PROVED here
                // proved for every value of `_0`, i.e. a tautology of the clause.
                if formula_refs_return_slot
                    && *path_prep.unmarked_sysroot_call.get_or_init(|| {
                        return_slot_written_by_unmarked_sysroot_call(vc_block, block)
                    })
                    && return_slot_only_in_negated_clause(&formula)
                {
                    vcs.push(contracts::unconstrained_return_call_vc(
                        func,
                        path_prep.vc_block_span.clone(),
                        &post,
                        clause_metadata,
                    ));
                    continue;
                }

                // Trust (P0 multi-write postcondition false-refutation, 2026-08-01)
                // — the OUT-PARAMETER twin of the return-slot tripwire above.
                //
                // A clause-mentioned `&mut`-parameter place that the body STORES TO
                // but that NO conjunct constrains at the token the obligation body
                // reads makes `Not(post)` satisfiable BY HAVOC: the row degenerates
                // into a refutable query over a free post-state and the full verifier
                // mints `verified_counterexample = true` against CORRECT code. That is
                // the worst failure mode a verifier has — it fails closed, so nothing
                // unsound ships, but it tells you your correct code is wrong. Fail to
                // the VISIBLE unsupported row instead of refuting.
                //
                // The pin lane's own ledger (`unpinned_out_params`) is necessary but
                // not sufficient to fire: another conjunct — a block def, a semantic
                // guard — may already constrain the place, in which case the VC is
                // still meaningful and must proceed. So each residue name is checked
                // against the ASSEMBLED formula under the exact version token the
                // obligation body carries, mirroring `formula_has_return_slot_pin`.
                //
                // Trust (2026-08-02): the ledger is widened from "the two
                // scanned blocks store it" to "the FUNCTION stores it", because
                // the narrow version had a hole exactly where the ladder's top
                // rung lives. `with_out_param_pins` scans only `[predecessor,
                // return block]`, so when the store sits further upstream —
                // `self.st.f = false` three blocks before the exit, with an
                // opaque `self.helper()` call on one arm in between — `required`
                // came back EMPTY, no tripwire fired, and the row was emitted as
                // a refutable query over the unconstrained join name. That row
                // then "refuted" the clause AND its exact negation identically,
                // which is the discrimination collapse itself: a silent gap,
                // reported as a verdict.
                //
                // `out_param_store_sorts` is the function-wide population, so a
                // clause-mentioned place the body writes ANYWHERE is now
                // accounted for. A place the body never writes is still absent
                // from it and stays genuinely refutable, which is what makes
                // `ensures self.n == 0` over an empty body correctly fail.
                let clause_written_out_params: std::borrow::Cow<'_, [String]> =
                    if unpinned_out_params.is_empty() {
                        std::borrow::Cow::Borrowed(base_clause_written_out_params)
                    } else {
                        let mut names = base_clause_written_out_params.to_vec();
                        names.extend(unpinned_out_params.iter().cloned());
                        if names.len() > 1 {
                            names.sort_unstable();
                            names.dedup();
                        }
                        std::borrow::Cow::Owned(names)
                    };
                let unconstrained_out_param = clause_written_out_params.iter().find(|subject| {
                    let versioned =
                        match sv.version_token_at(func, block.id, block.stmts.len(), subject) {
                            Some(tok) => format!("{subject}#{tok}"),
                            None => (*subject).clone(),
                        };
                    !formula_pins_var_name(&formula, &versioned)
                });
                if let Some(subject) = unconstrained_out_param {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        path_prep.vc_block_span.clone(),
                        &format!(
                            "postcondition references `&mut`-parameter place `{subject}`, which the \
                             body writes but no conjunct pins at the obligation's read version; \
                             refusing a refutable query over a free post-state"
                        ),
                        &format!("{post:?}"),
                        clause_metadata,
                    ));
                    continue;
                }

                // Trust (P0 dropped-entry-hypothesis postcondition
                // false-refutation, 2026-08-06) — the ENTRY-HYPOTHESIS sibling
                // of the two tripwires above.
                //
                // `gate_contract_preconditions` drops the WHOLE contract-derived
                // precondition set on any gate failure (a body local shadowing a
                // parameter debug name, a predicate outside the assumable
                // fragment, a predicate with no ground witness). Dropping is
                // correct there — assuming a fact that binds the wrong variable
                // is a false-PROVE. But this lane then assembles the
                // postcondition VC over an entry state that NOTHING constrains
                // beyond the always-true synthetic facts appended AFTER the gate
                // (integer/char/discriminant ranges). `Not(post)` becomes
                // satisfiable at an entry state the author's `requires` forbids,
                // the row is reported Failed, and the full verifier mints
                // `verified_counterexample = true` against CORRECT code —
                // measured on `#[requires(n >= 0)] #[ensures(|r| *r >= 0)] fn
                // f(n: i32) -> i32 { n }`, where the "counterexample" is
                // `n = -1`, a call the precondition forbids. Same doctrine as
                // the out-parameter twin: fail to the VISIBLE unsupported row
                // instead of refuting.
                //
                // PRECISION. The trigger is not "the gate dropped something" and
                // not "the clause mentions a constrained parameter" — either
                // would suppress rows that are perfectly meaningful without the
                // hypothesis. It is: EVERY counterexample that can be EXHIBITED
                // for this assembled row is an entry state the dropped
                // `requires` excludes (`only_excluded_counterexamples`). Firing
                // therefore requires a concrete model in hand, so:
                //   * a PROVABLE row has no model, none is found, and the row is
                //     emitted unchanged — `ensures(*ret >= n)` over `{ n }` with
                //     the same dropped `requires` still proves. "Provable" means
                //     provable as judged HERE, before the stored-value type ranges
                //     are conjoined below: a row that proves only through a
                //     carrier range (`ensures(*ret >= 0)` over `{ x }` for a
                //     `usize` `x`, with `x > 0` dropped) has the out-of-range
                //     model `x = -1`, which the dropped clause excludes, so it is
                //     refused. A fail-closed precision gap, kept on purpose:
                //     conjoining the ranges here would add their bounds to
                //     `candidate_ints` (a `u128` bound is no `i128` and declines
                //     outright; each bound adds three candidates against the
                //     32-candidate cap), so the search would DECLINE on rows it
                //     fires on today and emit exactly the refutation this
                //     tripwire suppresses (VCGEN-LIB-REDS-1);
                //   * a GENUINE bug whose counterexample satisfies the
                //     precondition is found to be genuine and still refutes —
                //     `requires(n >= 0)` with `ensures(|r| *r >= 5)` over `{ n }`
                //     admits `n == 0`, which the precondition allows.
                //
                // TWO NAMESPACES. The clause is written in the SOURCE's
                // spelling and this row in the BODY's, and they diverge exactly
                // where the gate drops: for `{ let x = n; x }`,
                // copy-propagation parks the body `let` on the parameter local
                // and the last-write-wins debug-name collapse names local 1
                // `x`, so the row reads `x`/`_0` while the clause reads `n` —
                // one entity, parameter position 1, under two spellings. A
                // spelling-only relevance test never connects them, which is
                // why that case still minted `verified_counterexample = true`
                // after the `__ret` fix. `forced_parameter_alias` recovers the
                // correspondence by parameter POSITION and declines whenever it
                // is not uniquely determined; the restatement it enables lives
                // and dies inside `only_excluded_counterexamples` (which
                // returns `bool`), so a clause the gate refused to assume can
                // never reach an emitted formula.
                //
                // The search is bounded and fragment-limited, and every failure
                // to decide declines to fire, so this is an INCOMPLETE fix by
                // construction: false refutations survive wherever a model
                // cannot be exhibited inside the fragment. That is an honest
                // gap, not a claim. The Machine{w} lane is excluded outright —
                // its emitted formula is the declared-width QF_BV translation
                // below, and a model of the mathematical-`Int` spelling is not
                // a model of that.
                //
                // Trust (a7 per-path split, 2026-09-18): this is the ONE decision
                // in this loop that does NOT distribute over the path-guard `Or`
                // — models of a disjunction are the UNION of the disjuncts'
                // models, so "every model is excluded" is strictly stronger for
                // the merged row than for any one path, and judging it on the
                // merged row while shipping per-path rows could emit exactly the
                // row this guard exists to suppress. The split therefore declines
                // outright on a function with a dropped `requires`; see
                // `split_declined_for_dropped_requires` above. The row this test
                // judges is then the only row emitted, exactly as at HEAD.
                if !*machine_lane
                    && !dropped_requires.is_empty()
                    && only_excluded_counterexamples(func, &formula, dropped_requires)
                {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        path_prep.vc_block_span.clone(),
                        "the authored `requires` was not assumed for body verification (see the \
                         `is not assumed for body verification` warning on this function), and \
                         every counterexample this row admits is an entry state that `requires` \
                         excludes; refusing a refutable query over an under-constrained entry \
                         state. To get a verdict, remove the reason the precondition was dropped: \
                         rename the body local that shadows the parameter, restate the predicate \
                         over the parameters directly, or replace an unsatisfiable predicate with \
                         one that has a witness",
                        &format!("{post:?}"),
                        clause_metadata,
                    ));
                    continue;
                }

                if *machine_lane {
                    match contracts::machine_faithful_vc_formula(func, &formula) {
                        Some(machine) => formula = machine,
                        None => {
                            vcs.push(contracts::spec_unverifiable_vc(
                                func,
                                path_prep.vc_block_span.clone(),
                                "machine-arithmetic ensures conjoined body facts outside the declared-width fragment",
                                &format!("{post:?}"),
                                clause_metadata,
                            ));
                            continue;
                        }
                    }
                    let translated: Option<Vec<Formula>> = path_split_rows
                        .iter()
                        .map(|row| contracts::machine_faithful_vc_formula(func, row))
                        .collect();
                    path_split_rows = translated.unwrap_or_default();
                }

                let rows = if path_split_rows.is_empty() { vec![formula] } else { path_split_rows };
                for row in rows {
                    let row = if *machine_lane {
                        row
                    } else {
                        conjoin_postcondition_value_type_ranges(func, row)
                    };
                    vcs.push(VerificationCondition {
                        kind: VcKind::Postcondition,
                        function: fn_sym,
                        location: path_prep.vc_block_span.clone(),
                        formula: row,
                        contract_metadata: clause_metadata,
                        obligation: None,
                    });
                }
            }
        }
    }

    vcs
}

/// Structural match between a TEXT-PARSED spec clause and the compiler's own
/// TYPED lowering of that same clause, forgiving ONLY the parser's
/// missing-type sentinel on a variable leaf.
///
/// WHY THIS EXISTS. `trust_types::parse_spec_expr` takes a bare `&str` and so
/// has no type environment at all: `Parser::variable` stamps every leaf it
/// cannot resolve from a quantifier binder with the default `Sort::Int`
/// (`trust-types/src/spec_parse.rs:793-802`). The compiler's contract lowering
/// carries the REAL sort. `Formula` derives structural `PartialEq`, and its
/// `Var(String, Sort)` / `SymVar(Symbol, Sort)` variants COMPARE THE SORT, so a
/// clause over a `bool` place can never equal a re-parse of its own source
/// text:
///
/// ```text
/// ensures !self.storage.f
///   typed lowering : Not(Var("self*.0.0", Bool))
///   re-parsed text : Not(Var("self*.0.0", Int))   <- differs ONLY in sort
/// ```
///
/// An integer clause matches by coincidence — the sentinel IS `Int` — which is
/// why the integer lane already proves and refutes at projection depth 1, 2 and
/// 3, while EVERY `bool` clause fails, at depth 1 exactly as much as at depth 2.
/// The mismatch is a sort bug, not a nesting bug.
///
/// SOUNDNESS. Everything except a variable's sort must match EXACTLY:
/// constructor, arity, every constant, every bitvector width, every quantifier
/// binder list, every predicate/constructor name, and every variable NAME. The
/// single relaxation is a leaf whose PARSED side carries `Sort::Int`, the
/// no-information default, which is allowed to meet any sort on the typed side.
/// A different place spells a different NAME and is still refused, so this can
/// never bind a clause to some other clause's place; it only lets a clause
/// recognize the text it was itself lowered from. Quantifier-bound leaves
/// cannot be mis-forgiven either: a binder list is non-child payload and is
/// compared exactly, and a binder declaring a non-`Int` sort is precisely what
/// makes the parser resolve that same sort instead of the sentinel.
///
/// The shape test is written against `Formula::map_children`/`Formula::children`
/// so it stays TOTAL over this `#[non_exhaustive]` enum: a variant added later
/// is compared exactly by construction, rather than silently falling into a
/// permissive catch-all arm.
pub(super) fn parsed_clause_matches_typed(parsed: &Formula, typed: &Formula) -> bool {
    // The sentinel's one consequence ABOVE a leaf (SPEC-FLOAT-EQ-STRUCTURAL-1).
    // A contract `==` is Rust `PartialEq`, so once its operands are known to be
    // floats the typed lowering spells it IEEE `FpEq`; between two bare
    // identifiers the parser cannot know that and spells it `Eq`. Same clause,
    // so the operands are matched pairwise under the same rules. One direction
    // only: a parsed `FpEq` (a float literal fixed the sort) must meet a typed
    // `FpEq`, and a typed structural `Eq` is never the lowering of either.
    if let (Formula::Eq(parsed_lhs, parsed_rhs), Formula::FpEq(typed_lhs, typed_rhs)) =
        (parsed, typed)
    {
        return parsed_clause_matches_typed(parsed_lhs, typed_lhs)
            && parsed_clause_matches_typed(parsed_rhs, typed_rhs);
    }
    // The one and only relaxation on a variable leaf.
    if let (Some((parsed_name, parsed_sort)), Some((typed_name, typed_sort))) =
        (formula_var_leaf(parsed), formula_var_leaf(typed))
    {
        return parsed_name == typed_name
            && (parsed_sort == typed_sort || *parsed_sort == Sort::Int);
    }
    // Identical constructor and identical non-formula payload, then identical
    // children pairwise.
    same_formula_shape(parsed, typed)
        && trust_types::all_formula_children_zip(parsed, typed, parsed_clause_matches_typed)
}

/// `Var` and `SymVar` viewed uniformly as `(name, sort)`. `SymVar` is
/// documented as the interned spelling of `Var` and semantically identical to
/// it, so a clause is allowed to match across the two spellings.
fn formula_var_leaf(formula: &Formula) -> Option<(&str, &Sort)> {
    match formula {
        Formula::Var(name, sort) => Some((name.as_str(), sort)),
        Formula::SymVar(symbol, sort) => Some((symbol.as_str(), sort)),
        _ => None,
    }
}

/// True iff two nodes share a constructor AND identical non-formula payload
/// (widths, binder lists, constants, interned names), ignoring their
/// sub-formulas.
///
/// Implemented by erasing every DIRECT child to one fixed sentinel and then
/// comparing structurally. This needs no per-variant match arm, so unlike a
/// hand-written enumeration it cannot go stale as `Formula` grows. A child that
/// happens to BE the sentinel is harmless: erasure decides the shape only, and
/// the caller still compares every child pairwise afterwards.
fn same_formula_shape(a: &Formula, b: &Formula) -> bool {
    if std::mem::discriminant(a) != std::mem::discriminant(b) {
        return false;
    }
    match (a, b) {
        (Formula::And(ca), Formula::And(cb)) | (Formula::Or(ca), Formula::Or(cb)) => {
            return ca.len() == cb.len();
        }
        (
            Formula::Not(_)
            | Formula::Neg(_)
            | Formula::Implies(_, _)
            | Formula::Eq(_, _)
            | Formula::Lt(_, _)
            | Formula::Le(_, _)
            | Formula::Gt(_, _)
            | Formula::Ge(_, _)
            | Formula::Add(_, _)
            | Formula::Sub(_, _)
            | Formula::Mul(_, _)
            | Formula::Div(_, _)
            | Formula::Rem(_, _)
            | Formula::BvConcat(_, _)
            | Formula::Select(_, _)
            | Formula::Ite(_, _, _)
            | Formula::Store(_, _, _),
            _,
        ) => return true,
        (
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Rat { .. }
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..)
            | Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_),
            _,
        ) => return a == b,
        _ => {}
    }
    fn erase(formula: &Formula) -> Formula {
        formula.clone().map_children(&mut |_| Formula::Bool(false))
    }
    erase(a) == erase(b)
}

/// Resolve one parsed formula to exactly one authored clause in the canonical
/// `VerifiableFunction::contracts` vector. Formula equality alone is never
/// enough to choose between duplicate clauses: ambiguity deliberately returns
/// `None`, leaving every corresponding source marker undischargeable.
pub(super) fn unique_source_contract_index_for_formula(
    func: &VerifiableFunction,
    expected_kind: ContractKind,
    formula: &Formula,
) -> Option<usize> {
    let mut matches = func.contracts.iter().enumerate().filter_map(|(index, contract)| {
        if contract.kind != expected_kind {
            return None;
        }
        let body = contract
            .body
            .strip_prefix(contracts::LOWERED_CONTRACT_PREFIX)
            .unwrap_or(&contract.body);
        // `formula` is the compiler's TYPED clause (this helper's only callers
        // pass `func.postconditions`); `parsed` is the re-parse of the authored
        // text. Sort-exact equality here silently denied every `bool` clause a
        // `source_contract_index`, and `trust_verify.rs:32245` needs that index
        // (`fresh_vc.contract_metadata?.source_contract_index?`) to build the
        // body link, without which the source-clause marker stays pending.
        // Ambiguity handling below is untouched: two matching clauses still
        // yield `None`.
        trust_types::parse_spec_expr(body)
            .map(|parsed| rebind_text_lengths(func, parsed))
            .filter(|parsed| parsed_clause_matches_typed(parsed, formula))
            .map(|_| index)
    });
    let index = matches.next()?;
    matches.next().is_none().then_some(index)
}

/// Add source-clause identity without turning the public routing metadata into
/// authority. The verifier-api bridge independently checks this index against
/// the canonical compiler contract before publishing a clause link.
pub(super) fn contract_metadata_with_source_index(
    base: Option<ContractMetadata>,
    source_contract_index: Option<usize>,
) -> Option<ContractMetadata> {
    let Some(source_contract_index) = source_contract_index else {
        return base;
    };
    let mut metadata = base.unwrap_or_default();
    metadata.source_contract_index = Some(source_contract_index);
    Some(metadata)
}

/// A statement-version of the return slot local 0: bare `_0` or a versioned
/// `_0#<tok>`. Deliberately does NOT match `_0.<field>` projections or any other
/// local (`_5`, `_10#...`), so unification touches ONLY the whole return value.
pub(super) fn is_return_slot_name(name: &str) -> bool {
    name == "_0" || name.starts_with("_0#")
}

/// Whether ANY conjunct on the formula's positive `And` spine is an equality
/// whose left-hand side is a return-slot variable (any SSA version) — i.e. the
/// return value is PINNED to some definition. Deliberately spine-only: an
/// equality inside the negated clause is the obligation, not a pin.
pub(super) fn formula_has_return_slot_pin(formula: &Formula) -> bool {
    match formula {
        Formula::And(conjuncts) => conjuncts.iter().any(formula_has_return_slot_pin),
        Formula::Eq(lhs, _) => {
            matches!(&**lhs, Formula::Var(name, _) if is_return_slot_name(name))
        }
        _ => false,
    }
}

/// Whether `formula`'s POSITIVE `And` spine defines `name` — an `Eq(Var(name), _)`
/// conjunct. The generic counterpart to [`formula_has_return_slot_pin`], used by the
/// out-parameter silent-weakening tripwire to ask "is this post-state place actually
/// constrained by SOME conjunct?" without caring which lane supplied it (the pin
/// loop, a block def, a semantic guard).
///
/// Deliberately spine-only, exactly as the return-slot twin: an equality buried
/// under `Not`/`Or`/`Implies` is a CLAIM, not a definition, and crediting it would
/// let the negated postcondition appear to constrain the very variable it is
/// interrogating — re-opening the free-variable hole this tripwire exists to close.
pub(super) fn formula_pins_var_name(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::And(conjuncts) => conjuncts.iter().any(|c| formula_pins_var_name(c, name)),
        // Trust: a DISJUNCTION pins the name only when EVERY arm does. The
        // path-guard lane wraps the assembled VC as `Or([And([guards.., body]),
        // ..])` — one arm per path to the predecessor — so a pin conjoined
        // before that wrap lands inside every arm and IS a pin, while an arm
        // that leaves the name free makes the whole row satisfiable by havoc
        // through that arm alone. Without this arm the test answered `false`
        // for every multi-path VC, which would fire the tripwire on rows whose
        // post-state is fully constrained.
        Formula::Or(arms) => {
            !arms.is_empty() && arms.iter().all(|a| formula_pins_var_name(a, name))
        }
        // Trust: a SELF-equality is not a pin. `x == x` constrains nothing, yet
        // it would satisfy the shape test and silently suppress the
        // silent-weakening tripwire — converting the VISIBLE fail-closed row
        // into exactly the invisible free-variable query the tripwire exists to
        // prevent. (A tautology can be assembled by a later whole-formula
        // rename collapsing both operands of a genuine pin onto one name.)
        Formula::Eq(lhs, rhs) => {
            matches!(&**lhs, Formula::Var(n, _) if n == name) && **lhs != **rhs
        }
        _ => false,
    }
}

/// Whether every projected return value used by `postcondition` has an exact,
/// independent definition on `formula`'s positive `And` spine.
///
/// This is the aggregate counterpart to [`formula_has_return_slot_pin`].  It is
/// deliberately stricter than "some `_0.*` equality exists": every referenced
/// projection must be present, an equality hidden under `Not`/`Or` is not a
/// definition, and a projection-to-projection cycle is not grounding.  A
/// postcondition that also mentions the whole `_0` must still satisfy the
/// whole-slot rule above; field pins cannot stand in for an aggregate value.
pub(super) fn formula_has_complete_return_projection_pins(
    formula: &Formula,
    postcondition: &Formula,
) -> bool {
    fn mentions_unsupported_value_sentinel(formula: &Formula) -> bool {
        trust_types::any_formula_node(formula, &mut |node| {
            matches!(
                node,
                Formula::Var(name, _)
                    if name.starts_with("__trust_unsupported_operand_") || name == "__unknown_operand"
            )
        })
    }

    let mut required: FxHashSet<&str> = FxHashSet::default();
    if !trust_types::all_formula_nodes(postcondition, &mut |node| {
        if let Formula::Var(name, _) = node {
            let base = name.split('#').next().unwrap_or(name);
            if base == "_0" {
                return false;
            } else if base.starts_with("_0.") {
                required.insert(base);
            }
        }
        true
    }) || required.is_empty()
    {
        return false;
    }

    fn collect_positive_projection_pins<'a>(formula: &'a Formula, pins: &mut FxHashSet<&'a str>) {
        match formula {
            Formula::And(conjuncts) => {
                for conjunct in conjuncts {
                    collect_positive_projection_pins(conjunct, pins);
                }
            }
            Formula::Eq(lhs, rhs) => {
                if let Formula::Var(name, _) = &**lhs {
                    let base = name.split('#').next().unwrap_or(name);
                    if base.starts_with("_0.")
                        && !formula_references_return_slot(rhs)
                        && !mentions_unsupported_value_sentinel(rhs)
                    {
                        pins.insert(base);
                    }
                }
            }
            _ => {}
        }
    }

    let mut pinned: FxHashSet<&str> = FxHashSet::default();
    collect_positive_projection_pins(formula, &mut pinned);
    required.is_subset(&pinned)
}

/// Whether the predecessor or the return block ends in a call whose destination is
/// the WHOLE return slot `_0` — the shape the call-model pins above handle and the
/// statement pin loop cannot see — to an UNMARKED SYSROOT callee.
///
/// Both restrictions keep rows other lanes may still decide. A callee path the
/// extractor stamped with one of the MODELED `@trust-…` prefixes
/// ([`callee_carries_a_modeled_stamp`]) is one some lane models — the inferred-return
/// check hands exactly such a row (`_0 = wrapping_add(a, b)`, `_0` free in this
/// formula) to the Clean kernel. A user callee may be composed through its own
/// certified contract. A sysroot method that carries no marker
/// (`i32::unsigned_abs`, `u128::saturating_add`) has neither; an absent `callee_key`
/// is not evidence of one, so it does not fire.
///
/// Trust (std-call-summaries P2 review, 2026-10-12): the exemption used to be ANY
/// `@`-prefixed callee. The panic-freedom-only intrinsic stamp
/// (`@trust-rustc-panic-free-intrinsic::`) is modeled by NO lane — its result is a
/// fresh havoc by design — so `_0 = minimumf64(x, 0.0)` left `_0` free and the row
/// was a refutable query over havoc. The modeled stamps are now listed positively;
/// any other `@` spelling (the panic-free stamp, `@trust-total-to-string::`,
/// `@trust-indirect-callee`) fires. Firing can only withhold a verdict.
fn callee_carries_a_modeled_stamp(callee: &str) -> bool {
    [
        trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX,
        trust_types::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX,
        trust_types::TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX,
        trust_types::TRUST_RUSTC_WRAPPING_REFUTATION_METHOD_PATH_PREFIX,
    ]
    .iter()
    .any(|prefix| callee.starts_with(prefix))
}

fn return_slot_written_by_unmarked_sysroot_call(
    vc_block: &trust_types::BasicBlock,
    block: &trust_types::BasicBlock,
) -> bool {
    [vc_block, block].into_iter().any(|b| {
        matches!(&b.terminator, Terminator::Call { func: callee, dest, callee_key, .. }
            if dest.local == 0
                && dest.projections.is_empty()
                && !callee_carries_a_modeled_stamp(callee)
                && callee_key.as_ref().is_some_and(|key| key.krate_is_real_sysroot))
    })
}

/// Whether the return slot is constrained by NOTHING but the negated clause: on the
/// positive `And` spine exactly one conjunct mentions a return-slot variable, and
/// it is a `Not` (the clause); an `Or` on the spine (the path-guard wrap) answers
/// this for every arm. Anything else that mentions `_0` — a pin, a guarded model
/// equality, a callee fact, a second negation — is a constraint, and answers
/// `false`.
fn return_slot_only_in_negated_clause(formula: &Formula) -> bool {
    fn scan_spine<'f>(formula: &'f Formula, sole: &mut Option<&'f Formula>) -> Result<(), ()> {
        match formula {
            Formula::And(conjuncts) => {
                for c in conjuncts {
                    scan_spine(c, sole)?;
                }
                Ok(())
            }
            other => {
                if formula_references_return_slot(other) {
                    if sole.is_some() {
                        return Err(());
                    }
                    *sole = Some(other);
                }
                Ok(())
            }
        }
    }
    let mut sole = None;
    if scan_spine(formula, &mut sole).is_err() {
        return false;
    }
    match sole {
        Some(Formula::Not(_)) => true,
        Some(Formula::Or(arms)) => {
            !arms.is_empty() && arms.iter().all(return_slot_only_in_negated_clause)
        }
        _ => false,
    }
}

/// Whether a clause formula references the return slot (`_0`, a versioned
/// `_0#<tok>`, or a projected `_0.<field>` spelling) anywhere.
pub(super) fn formula_references_return_slot(formula: &Formula) -> bool {
    trust_types::any_formula_node(formula, &mut |node| {
        if let Formula::Var(name, _) = node {
            let base = name.split('#').next().unwrap_or(name);
            base == "_0" || base.starts_with("_0.")
        } else {
            false
        }
    })
}

/// Stamp only the clause's scalar result read with this return path's final value.
///
/// A Return block can join several writers, while each emitted row covers one
/// predecessor. Its clause must therefore use that predecessor's value, unless
/// the Return block writes a newer value itself. Do this before adding body facts:
/// an earlier `_0` read in a guard is a different value and must stay different.
/// In particular, neither a pin hidden under `Or` nor a historical pin on the
/// positive `And` spine is authority to rename all return-slot versions.
fn postcondition_at_return_path(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    pred: &trust_types::BasicBlock,
    ret: &trust_types::BasicBlock,
    clause: Formula,
) -> Option<Formula> {
    if !trust_types::any_free_variable_name(&clause, &mut |name| name == "_0") {
        return Some(clause);
    }
    let ret_token = sv.version_token_at(func, ret.id, ret.stmts.len(), "_0");
    let token = if pred.id == ret.id || ret_token != sv.version_token_at(func, ret.id, 0, "_0") {
        ret_token
    } else if terminator_def_names(func, pred).iter().any(|name| write_rebinds(name, "_0")) {
        // Terminator destinations are written after the predecessor's last
        // statement. This is the same establish token as its semantic facts.
        Some(format!("s{}_t", pred.id.0))
    } else {
        sv.version_token_at(func, pred.id, pred.stmts.len(), "_0")
    };
    // An absent token is not evidence of an initialized entry value. Leave a
    // visible unsupported row instead of letting a later rename bind `_0` to
    // a different predecessor's value.
    let result_name = format!("_0#{}", token?);
    let sort = crate::place_sort(func, &Place::local(0)).unwrap_or(Sort::Int);
    Some(crate::quantifier_tiers::finite_domain::substitute(
        &clause,
        "_0",
        &Formula::var_owned(result_name, sort),
    ))
}

/// Remove the explicit outer return pin only when an AST-identical `_0 == value`
/// pin is already an unconditional conjunct of its body.
///
/// The duplicate can become visible only after return-alias substitution and SSA
/// normalization, so this runs at the end of the postcondition builder.  Walking
/// only through `And` nodes is load-bearing: an equal-looking pin beneath `Or`,
/// `Not`, or an implication is conditional and must not suppress the outer pin.
pub(super) fn dedup_identical_return_slot_pin(formula: Formula) -> Formula {
    formula.map(&mut |node| {
        let Formula::And(conjuncts) = &node else {
            return node;
        };
        let [outer_pin, body] = conjuncts.as_slice() else {
            return node;
        };
        let is_return_pin = matches!(outer_pin, Formula::Eq(lhs, _)
            if lhs.var_name() == Some("_0"));
        if is_return_pin && unconditional_and_spine_contains(body, outer_pin) {
            body.clone()
        } else {
            node
        }
    })
}

pub(super) fn unconditional_and_spine_contains(formula: &Formula, expected: &Formula) -> bool {
    formula == expected
        || matches!(formula, Formula::And(conjuncts)
            if conjuncts
                .iter()
                .any(|conjunct| unconditional_and_spine_contains(conjunct, expected)))
}

// =========================================================================
// OUT-PARAMETER PIN
// =========================================================================
//
// `ensures` over a place reached through a `&mut` PARAMETER — `*x`,
// `(*self).0`, `(*self).0.3` — names a place the CALLER can observe at return,
// so the clause legitimately talks about the place's FINAL value. (This is the
// exact opposite of the hunt-6 by-value-parameter hazard above, where the
// clause snapshots the ENTRY value and the body-aware lane must therefore stay
// fail-closed. A by-value parameter is not reachable through a `Deref`, so the
// two lanes cannot overlap.)
//
// SOUNDNESS. The pin asserts one thing: "immediately after statement `k`, the
// place named `subject` holds the value statement `k` stored there". That is
// the definition of the assignment, so the fact is true by construction. Three
// properties keep it from ever admitting a false proof:
//
//   1. THE VALUE COMES FROM THE BODY, NEVER FROM THE CLAUSE. The rhs is the
//      statement's own lowered rvalue. A FALSE postcondition therefore stays
//      refutable: the place is pinned to its genuine value and `Not(clause)`
//      remains satisfiable. A pin can never be minted from what the clause
//      asserts, so it cannot vacuously discharge anything.
//
//   2. LIVENESS IS DECIDED BY THE SAME ORACLE THAT RENAMES THE OBLIGATION.
//      The pin is emitted ONLY when the defining statement's own version token
//      `s{block}_{k}` is byte-equal to the token `StmtVersionCtx` mints for the
//      body's read of `subject` at the use point. `version_token_at` already
//      accounts for later same-block writes, opaque-deref havoc
//      (`deref_store_havoc_names`), and inter-block call havoc (the entry map's
//      `s{pred}_t` tokens). If ANY of those intervene the tokens differ and no
//      pin is emitted — the VC degrades to exactly today's fail-closed
//      behaviour. We never re-derive liveness with a second, forkable rule.
//
//   3. ALIASING IS NOT ASSUMED AWAY. The pin claims nothing about any name
//      other than the one the statement literally writes. A store through some
//      other opaque pointer that could alias `subject` is reported by
//      `stmt_writes_name` as a write of `subject`, which moves the body's token
//      and suppresses the pin by (2).
//
// Reads inside the pinned rvalue are versioned at the read-point `k` (the values
// BEFORE the defining write), mirroring `version_block_def_at_establish`, so a
// self-referential store (`*x = *x + 1`) pins `x*_new == x*_old + 1` rather than
// the unsatisfiable `x* == x* + 1`.

/// Collect base (unversioned) variable sorts in `formula`: a base name spelled at two
/// different sorts maps to `None` (ambiguous).
fn collect_clause_base_sorts(formula: &Formula) -> FxHashMap<String, Option<Sort>> {
    let mut clause_sorts: FxHashMap<String, Option<Sort>> = FxHashMap::default();
    trust_types::visit_formula_nodes(formula, &mut |node| {
        if let Formula::Var(name, sort) = node {
            let base = name.split('#').next().unwrap_or(name);
            if let Some(slot) = clause_sorts.get_mut(base) {
                if slot.as_ref() != Some(sort) {
                    *slot = None;
                }
            } else {
                clause_sorts.insert(base.to_string(), Some(sort.clone()));
            }
        }
    });
    clause_sorts
}

/// True iff `place` is an OUT-PARAMETER place: the pointee of a `&mut`
/// reference PARAMETER, followed by zero or more FIELD projections.
///
/// Deliberately narrow. `Index`/`ConstantIndex`/`Subslice` are excluded (an
/// element name can alias a sibling under a symbolic index); `Downcast` is
/// excluded (an enum field's place is variant-dependent); raw pointers are
/// excluded (provenance is not tracked here); a SHARED `&` is excluded (nothing
/// can be stored through it, so there is nothing to pin). Anything excluded
/// simply yields no pin, which is the current behaviour.
fn is_out_param_place(func: &VerifiableFunction, place: &Place) -> bool {
    let Some((Projection::Deref, rest)) = place.projections.split_first() else {
        return false;
    };
    if !rest.iter().all(|p| matches!(p, Projection::Field(_))) {
        return false;
    }
    if !is_parameter(func, place.local) {
        return false;
    }
    // A duplicated declaration index makes the type ambiguous; `unique_local_decl` refuses.
    let Some(decl) = crate::unique_local_decl(func, place.local) else { return false };
    matches!(decl.ty, Ty::Ref { mutable: true, .. })
}

/// Every `&mut`-PARAMETER place the body STORES TO, keyed by the name the
/// contract parser spells it with, valued by the place's sort.
///
/// This is the population the postcondition lane can legitimately reason about
/// as a POST-STATE: a place the body never writes is not a post-state at all
/// (`ensures self.n == 0` over an empty body is genuinely refutable and must
/// stay so), and a place reached other than through a `&mut` parameter is
/// excluded by `is_out_param_place` for the reasons documented there.
///
/// A name STORED AT TWO DIFFERENT SORTS is dropped: the sort disagreement means
/// the name cannot be unified with the clause's reading of it, and guessing
/// would risk pinning a Bool place under an Int reading.
fn out_param_store_sorts(func: &VerifiableFunction) -> FxHashMap<String, Option<Sort>> {
    let mut sorts: FxHashMap<String, Option<Sort>> = FxHashMap::default();
    for param_local in 1..=func.body.arg_count {
        if !matches!(crate::local_ty_ref(func, param_local), Some(Ty::Ref { mutable: true, .. })) {
            continue;
        }
        crate::visit_local_write_stmts(
            func,
            &func.body.blocks,
            param_local,
            |_block, stmt| {
                let Statement::Assign { place, .. } = stmt else {
                    return;
                };
                if place.local != param_local || !is_out_param_place(func, place) {
                    return;
                }
                let Some(sort) = crate::place_sort(func, place) else { return };
                sorts
                    .entry(crate::place_to_var_name(func, place))
                    .and_modify(|slot| {
                        if slot.as_ref() != Some(&sort) {
                            *slot = None;
                        }
                    })
                    .or_insert(Some(sort));
            },
        );
    }
    sorts
}

/// The condition on the control-flow edge `pred -> ret`, as a DISJUNCTION.
///
/// The early-return path's postcondition is true BECAUSE of this guard —
/// `if !self.st.f { return; }` returns only when the flag is ALREADY false, so
/// the clause holds trivially there — and no existing lane supplies it. The
/// path-guard lane keys on `vc_block` (`guard_paths_map.get(&vc_block.id)`), so
/// it contributes the guards that reach the PREDECESSOR and stops: the one edge
/// that selects THIS return is precisely the edge it drops. On the ladder's
/// minimal reproducer the predecessor is the ENTRY block, whose guard set is
/// empty, so the VC carried no branch information whatsoever.
///
/// SOUNDNESS — THE DISJUNCTION IS LOAD-BEARING. A `switchInt` may reach the same
/// target on several values (`0 | 1 => return`). Conjoining those guards would
/// assert `discr == 0 && discr == 1`: an UNSATISFIABLE premise makes the whole
/// VC vacuously UNSAT, which the "SAT iff violation" convention reads as PROVED
/// — a false proof minted out of nothing. The disjunction is the true edge
/// condition. An edge that is also reachable UNGUARDED (`Goto`, a `Call` /
/// `Assert` success edge) constrains nothing at all, so `None` is returned and
/// no premise is added.
///
/// Returned BARE (unversioned) on purpose: the caller re-runs
/// `v2_formula_with_block_defs` at `pred`'s terminal point, which stamps the
/// guard's reads at exactly the program point they are evaluated — the same
/// treatment `v2_formula_with_path_guards` gives every other path guard.
fn return_edge_guard(
    func: &VerifiableFunction,
    pred: &trust_types::BasicBlock,
    ret: BlockId,
) -> Option<Formula> {
    if !v2_terminator_has_target(&pred.terminator, ret) {
        return None;
    }
    // Reachable without taking any guarded clause: the edge asserts nothing.
    if pred.terminator.has_unguarded_successor(ret) {
        return None;
    }
    let mut disjuncts: Vec<Formula> = Vec::new();
    for guarded in pred.terminator.discovered_clauses(pred.id) {
        if matches!(guarded.target, trust_types::ClauseTarget::Block(t) if t == ret) {
            disjuncts.push(guards::guard_to_formula(func, &guarded.guard));
        }
    }
    match disjuncts.len() {
        0 => None,
        1 => disjuncts.pop(),
        _ => Some(Formula::Or(disjuncts)),
    }
}

/// The REACHING-VALUE IDENTITY across one return edge, for every
/// `&mut`-parameter place the clause mentions.
///
/// `place#<join token at the return block> == place#<token at this
/// predecessor's exit>`.
///
/// This VC is generated ONCE PER RETURN PREDECESSOR, so it quantifies exactly
/// over the executions that enter `ret` through `pred`. Along every one of
/// those, the place's value at `ret`'s entry IS its value at `pred`'s exit —
/// nothing else runs in between. The equality is therefore a TRUE fact of every
/// execution this row covers, and conjoining it removes only models that
/// correspond to NO execution. It can turn a spurious refutation into a proof;
/// it cannot make a violated clause unsatisfiable, because the predecessor-side
/// token is itself constrained only by the body's own stores (the same-block pin
/// lane and the block defs), never credited with a value the body did not write.
///
/// THREE GATES KEEP THE EQUALITY TRUE. Each one, if dropped, would be a false-
/// PROOF vector, not merely a precision loss:
///
///   1. THE RETURN BLOCK MUST NOT WRITE THE PLACE before the use point. If it
///      does, the obligation reads that block's OWN establish token and the
///      predecessor's exit value is stale — pinning them equal would assert
///      that a store did not happen. Checked by requiring the use-point token to
///      equal the block's ENTRY token (`stmt_idx = 0`), i.e. by asking the SAME
///      oracle that renamed the obligation rather than re-deriving liveness with
///      a second, forkable rule.
///
///   2. THE PREDECESSOR'S TERMINATOR MUST NOT WRITE THE PLACE. A `Call` taking
///      `&mut self` runs AFTER the block's statements, so the post-statement
///      value is not what reaches `ret`. `terminator_def_names` is the same
///      oracle the path-def lane kills stale facts with, and each of its names is
///      tested against the subject through `write_rebinds(term_def, subject)` —
///      the DIRECTIONAL write/read relation, written name FIRST. That test carries
///      TWO channels, and the gate needs both:
///
///        * ANCESTOR (and descendant) HAVOC, via the symmetric
///          `place_names_overlap` core: `self` covers `self*.0.0`, and a
///          symbolic-index write covers its array-base siblings.
///        * A WRITE OF AN INDEX LOCAL, via `write_covers_index_segment`: a `Call`
///          whose dest is the WHOLE local `l` and that is used as an index operand
///          somewhere in the body contributes the fallback spelling `_l` to
///          `terminator_def_names` (`push_index_fallback_name`), and that name
///          rebinds every subject carrying the segment `[_l]` — `s*[_l]`,
///          `s*[_l]__slice_len`, anything projected below it. This channel is NOT
///          symmetric and is not reachable from `place_names_overlap`, which is why
///          the gate must call the relation with the written name first rather than
///          testing overlap.
///
///   3. THE TWO TOKENS MUST DIFFER. An equal pair is the single-predecessor
///      case already owned by the same-block pin lane, and emitting `x == x`
///      there would be worse than useless: `formula_pins_var_name` would count
///      the tautology as a pin and suppress the silent-weakening tripwire,
///      converting a VISIBLE fail-closed row into an invisible free-variable
///      query.
///
/// COMPLETENESS IS UNTOUCHED. A genuinely violating execution reaches the return
/// block through SOME predecessor, and that predecessor's own row still captures
/// it with its own pins — which is why the false twin of every ladder rung still
/// refutes, from the body's genuine stored value rather than from havoc.
/// The plain locals this return block stores into the RETURN SLOT's fields
/// through a single `_0 = Aggregate(..)` statement, with their sorts.
///
/// These are subjects a clause can reach ONLY through the field pin: it names
/// `_0.0`, never the temp feeding it, so `clause_sorts` can never see them and
/// the `&mut`-parameter population never contains them. Without a merge pin
/// their reaching-def JOIN name (`c#s1_0_s2_0`) is free, and a TRUE clause over
/// the field is refuted by havoc -- see `aggregate_field_join_version_tests`.
///
/// Deliberately narrow: the store must target the bare return slot, and each
/// operand must be a projection-free local, so the pin can only ever talk about
/// a value one named local holds.
fn return_slot_aggregate_operand_sorts(
    func: &VerifiableFunction,
    ret: &trust_types::BasicBlock,
) -> FxHashMap<String, Option<Sort>> {
    let mut sorts: FxHashMap<String, Option<Sort>> = FxHashMap::default();
    for stmt in &ret.stmts {
        let Statement::Assign { place, rvalue: Rvalue::Aggregate(_, operands), .. } = stmt else {
            continue;
        };
        if place.local != 0 || !place.projections.is_empty() {
            continue;
        }
        for op in operands {
            let (Operand::Copy(operand_place) | Operand::Move(operand_place)) = op else {
                continue;
            };
            if !operand_place.projections.is_empty() {
                continue;
            }
            let Some(sort) = crate::place_sort(func, operand_place) else { continue };
            sorts
                .entry(crate::place_to_var_name(func, operand_place))
                .and_modify(|slot| {
                    if slot.as_ref() != Some(&sort) {
                        *slot = None;
                    }
                })
                .or_insert(Some(sort));
        }
    }
    sorts
}

fn return_edge_merge_pins(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    pred: &trust_types::BasicBlock,
    ret: &trust_types::BasicBlock,
    clause_sorts: &FxHashMap<String, Option<Sort>>,
    out_params: &FxHashMap<String, Option<Sort>>,
    agg_operands: &FxHashMap<String, Option<Sort>>,
) -> (Vec<Formula>, Vec<Formula>) {
    if (out_params.is_empty() || clause_sorts.is_empty()) && agg_operands.is_empty() {
        return (Vec::new(), Vec::new());
    }
    // Gate 2: anything the predecessor's TERMINATOR can write is off limits.
    let mut term_defs: Option<Vec<String>> = None;

    let mut subjects: Vec<&String> =
        Vec::with_capacity(out_params.len().min(clause_sorts.len()) + agg_operands.len());
    if !out_params.is_empty() {
        subjects.extend(
            clause_sorts
                .keys()
                .filter(|k| out_params.get(*k).is_some_and(Option::is_some)),
        );
    }
    subjects.extend(
        agg_operands
            .iter()
            .filter_map(|(k, sort)| sort.is_some().then_some(k)),
    );
    if subjects.is_empty() {
        return (Vec::new(), Vec::new());
    }
    subjects.sort_unstable();
    subjects.dedup();

    let mut pins = Vec::new();
    let mut grounds = Vec::new();
    for subject in subjects {
        // Two disjoint populations. An OUT-PARAMETER subject is a place the body
        // stores to through a `&mut` parameter AND that the clause reads, at an
        // agreeing sort -- the original discipline, unchanged. An AGGREGATE-FIELD
        // subject is a projection-free local feeding the return slot's aggregate
        // store; the clause cannot name it, so no clause-sort agreement exists to
        // check and none is required.
        let (place_sort, plain_local) = match out_params.get(subject) {
            Some(Some(place_sort))
                if clause_sorts.get(subject).and_then(Option::as_ref) == Some(place_sort) =>
            {
                (place_sort, false)
            }
            _ => match agg_operands.get(subject) {
                Some(Some(sort)) => (sort, true),
                _ => continue,
            },
        };
        if term_defs
            .get_or_insert_with(|| terminator_def_names(func, pred))
            .iter()
            .any(|d| write_rebinds(d, subject))
        {
            continue; // gate 2
        }
        let use_tok = sv.version_token_at(func, ret.id, ret.stmts.len(), subject);
        // Gate 1: the use-point token must BE the return block's entry token —
        // otherwise the return block itself rewrote the place.
        if use_tok != sv.version_token_at(func, ret.id, 0, subject) {
            continue;
        }
        let Some(use_tok) = use_tok else { continue };
        let pred_tok = sv.version_token_at(func, pred.id, pred.stmts.len(), subject);
        if pred_tok.as_deref() == Some(use_tok.as_str()) {
            continue; // gate 3
        }
        // GATE 4 — NEVER TRADE A VISIBLE GAP FOR AN INVISIBLE ONE. The pin makes
        // the join name a constrained name, which is exactly what the
        // silent-weakening tripwire below tests for; emitting it when the
        // PREDECESSOR side is itself an ungrounded havoc would suppress the
        // VISIBLE fail-closed row and leave the same refutable query over a free
        // post-state, now invisible. So the predecessor side must be one of the
        // two shapes this lane can actually account for:
        //
        //   * `None` — the ENTRY value (bare; see the Phase 1.3 note below). The
        //     row then says "the post-state IS the
        //     pre-state", which is the literal truth of an early-return path and
        //     is what lets the return-edge guard decide the clause. A clause the
        //     guard does NOT decide stays genuinely refutable, as it must.
        //   * a SINGLE statement establish token `s{b}_{k}` — one store reaches
        //     `pred`'s exit along every path, so that store certainly executed
        //     and its value can be pinned (below).
        //
        // A JOIN token (several stores reach) or a terminator havoc token
        // (`s{b}_t`) grounds nothing: no pin is emitted and the row keeps
        // today's fail-closed behaviour.
        let ground = match &pred_tok {
            None => None,
            Some(tok) => match store_at_token(func, sv, subject, tok, plain_local) {
                Some(fact) => Some(fact),
                None => continue,
            },
        };
        // Trust (2026-09-30, vac Phase 1.3 audit — DOCUMENTED, not sealed): the
        // ENTRY-valued predecessor side stays BARE, and that is sound because every
        // whole-formula rename this pin ever meets is at the PREDECESSOR END
        // `(pred, pred.stmts.len())` — the `v2_formula_with_block_defs(vc_block, ..)`
        // re-run right after it is conjoined and `conjoin_preconditions_versioned`
        // at `vc_block` — where `pred_tok` is `None`, so each rename is the identity
        // on it (path guards are renamed per guard, and `normalize_ssa_version_tokens`
        // only collapses whole locals that are single-assignment). The bare name is
        // thus exactly the `Fact::entry` spelling. What regressed the early-return
        // shape under Phase 0 was not this pin but the REFUSED TIE: the guard def is
        // sealed to `_2 == self*.0.0#e`, and `entry_sentinel_tie_is_sound` (widened
        // in Phase 1.1 to a token-less consumer whose reaching union is exactly
        // `{e}`) now ties `self*.0.0#e == self*.0.0`, reconnecting the two spellings.
        // Should a rename at any OTHER point ever be added after this conjoin, this
        // operand must be sealed (`seal_bare_reads` at the predecessor end) first.
        let pred_name = match &pred_tok {
            Some(tok) => format!("{subject}#{tok}"),
            None => subject.clone(),
        };
        pins.push(Formula::Eq(
            Box::new(Formula::var_owned(format!("{subject}#{use_tok}"), place_sort.clone())),
            Box::new(Formula::var_owned(pred_name, place_sort.clone())),
        ));
        grounds.extend(ground);
    }
    (pins, grounds)
}

/// The defining equation of the store that mints `subject#{token}`, when
/// `token` names one — `subject#s{b}_{k} == <the rvalue of block b's statement
/// k>`.
///
/// The out-parameter pin lane refuses this whenever the obligation's own read
/// token differs from the store's (its liveness gate), which is correct for a
/// SAME-BLOCK pin but leaves the multi-block case with nothing: on the ladder's
/// top rung the flag is stored three blocks upstream of the exit, so no lane
/// scanning `[predecessor, return block]` can ever see it. The merge pin above
/// supplies the missing link `join == s{b}_{k}`; this supplies the value.
///
/// SOUNDNESS. `subject#s{b}_{k}` is the SSA name for the value block `b`'s
/// statement `k` stores, so the equation is that statement's own semantics — it
/// pins the place to the value the BODY writes and can never credit a value the
/// body did not write, which is why the false twin of every rung still refutes.
/// The caller has already established that this token is the SINGLE reaching
/// definition at the predecessor's exit, so the store certainly executed on
/// every execution this row covers. Reads inside the rvalue are versioned at the
/// read-point `k` — the values BEFORE this write — so a self-referential store
/// (`*x = *x + 1`) yields `x*_new == x*_old + 1` rather than the unsatisfiable
/// `x* == x* + 1`, exactly as `with_out_param_pins` does.
///
/// Returns `None` — no pin, fail closed — for anything outside that shape: a
/// token that is not a single statement establish token, a statement that does
/// not store `subject`, a `CheckedBinaryOp` or array-theory store (owned by
/// their own encodings), or an rvalue the encoder cannot lower.
/// Trust (2026-09-30, P2 of the `vac` root cause): stamp every bare read of a
/// postcondition RETURN-VALUE pin at the pin's OWN statement `(def_block, k)`.
///
/// The pins used to be conjoined bare and stamped by whichever whole-formula
/// rename ran next — the predecessor-end rename of `conjoin_preconditions_versioned`
/// (TOO EARLY for a Return-block write before the pin: `ext(t); s.f = !t; s.f`
/// read the pre-write `s.f`) or a Return-block re-run of
/// `v2_formula_with_block_defs` (TOO LATE for a write after the pin: `let t = s.f;
/// s.f = c; t` read the post-write `s.f`). Each proved a false `ensures`.
///
/// Per bare name `n`, including a read of an older return-slot value:
///  * a pin in the Return block with a separate predecessor, when the Return
///    block has not written `n` before `k` and the predecessor's terminator does
///    not rebind it, resolves at the PREDECESSOR END — exactly today's
///    per-predecessor spelling, so a join-token pin is unchanged;
///  * otherwise it resolves at `(def_block, k)`.
///
/// A token found becomes `n#tok`; no token SEALS `n` at the resolution point
/// (`seal_bare_reads`). `None` (drop the pin — fail closed) on a seal collision.
fn stamp_return_pin_reads(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    vc_block: &trust_types::BasicBlock,
    block: &trust_types::BasicBlock,
    def_block: &trust_types::BasicBlock,
    k: usize,
    f: Formula,
) -> Option<Formula> {
    let in_return_block = def_block.id == block.id && block.id != vc_block.id;
    let pred_term = in_return_block.then(|| sv.terminator_kill(func, vc_block));
    let mut failed = false;
    let stamped = f.map(&mut |node| match node {
        Formula::Var(ref name, _) if !name.contains('#') => {
            let per_predecessor = pred_term.as_ref().is_some_and(|term| {
                sv.version_token_at(func, block.id, k, name)
                    == sv.version_token_at(func, block.id, 0, name)
                    && term.survives(&node)
            });
            let (at_block, at_point) = if per_predecessor {
                (vc_block.id, vc_block.stmts.len())
            } else {
                (def_block.id, k)
            };
            let Formula::Var(mut name, sort) = node else { return node };
            match sv.version_token_at(func, at_block, at_point, &name) {
                Some(tok) => {
                    name.reserve(1 + tok.len());
                    name.push('#');
                    name.push_str(&tok);
                    Formula::Var(name, sort)
                }
                None if is_return_slot_name(&name) => {
                    failed = true;
                    Formula::Var(name, sort)
                }
                None => match seal_bare_reads(sv, func, at_block, at_point, Formula::Var(name, sort))
                {
                    Some(sealed) => sealed,
                    None => {
                        failed = true;
                        Formula::Bool(false)
                    }
                },
            }
        }
        other => other,
    });
    (!failed).then_some(stamped)
}

fn store_at_token(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    subject: &str,
    token: &str,
    plain_local: bool,
) -> Option<Formula> {
    let (block_part, stmt_part) = token.strip_prefix('s')?.split_once('_')?;
    let block_idx: usize = block_part.parse().ok()?;
    let stmt_idx: usize = stmt_part.parse().ok()?;
    let block = func.body.blocks.get(block_idx).filter(|b| b.id.0 == block_idx)?;
    let stmt = block.stmts.get(stmt_idx)?;
    let Statement::Assign { place, rvalue, .. } = stmt else { return None };
    if crate::place_to_var_name(func, place) != subject {
        return None;
    }
    // An out-parameter subject keeps the original place gate. An aggregate-field
    // subject is a projection-free local instead -- still a single named place
    // whose store this equation reproduces, never a deref or a field write.
    if !if plain_local { place.projections.is_empty() } else { is_out_param_place(func, place) } {
        return None;
    }
    if matches!(rvalue, Rvalue::CheckedBinaryOp(..))
        || crate::is_array_theory_element_store(func, place.local, stmt)
    {
        return None;
    }
    let sort = crate::place_sort(func, place)?;
    let value = crate::chc::rvalue_to_formula(func, rvalue).ok()?;
    let value = version_rename_owned_at(value, sv, func, block.id, stmt_idx);
    // Trust (2026-09-30, stale-read seal): reads still bare at the store would be
    // re-stamped by a later whole-formula rename; seal them, or emit no pin.
    let value = seal_bare_reads(sv, func, block.id, stmt_idx, value)?;
    Some(Formula::Eq(
        Box::new(Formula::var_owned(format!("{subject}#{token}"), sort)),
        Box::new(value),
    ))
}

/// Conjoin out-parameter pins onto `formula`.
///
/// `use_block` is the block whose end-of-statements point the obligation body was
/// versioned at; `def_blocks` are the blocks scanned for the defining store (the
/// VC's predecessor and the return block, matching the return-slot pin above).
fn with_out_param_pins(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    use_block: &trust_types::BasicBlock,
    def_blocks: &[&trust_types::BasicBlock],
    clause_sorts: &FxHashMap<String, Option<Sort>>,
    mut formula: Formula,
) -> (Formula, Vec<String>) {
    if clause_sorts.is_empty() {
        return (formula, Vec::new());
    }

    let use_point = use_block.stmts.len();
    let mut pinned: FxHashSet<String> = FxHashSet::default();
    // Trust (P0 multi-write postcondition false-refutation, 2026-08-01) — the
    // SILENT-WEAKENING ledger. `required` is every clause-mentioned out-param place
    // the body ACTUALLY STORES TO (recorded BEFORE the liveness gate below);
    // `pinned_bases` is the subset that ended up constrained. The difference is a
    // post-state this lane failed to capture, which the caller must fail CLOSED on
    // rather than emit as a refutable query over a free variable. Deliberately keyed
    // on "the body stores to it": a clause-mentioned place the body NEVER writes
    // (`ensures self.n == 0` over an empty body) is GENUINELY refutable and must
    // stay so.
    let mut required: FxHashSet<String> = FxHashSet::default();
    let mut pinned_bases: FxHashSet<String> = FxHashSet::default();

    for def_block in def_blocks {
        for (k, stmt) in def_block.stmts.iter().enumerate() {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if !is_out_param_place(func, place) {
                continue;
            }
            // Leave the lanes that own their own encoding alone: a
            // CheckedBinaryOp's value is pinned by its assert-passed semantic
            // guard, and an array-theory element store is modeled as a `Store`
            // term under its own version scheme.
            if matches!(rvalue, Rvalue::CheckedBinaryOp(..))
                || crate::is_array_theory_element_store(func, place.local, stmt)
            {
                continue;
            }
            let subject = crate::place_to_var_name(func, place);
            // The clause must actually mention this place, at a sort that agrees
            // with the place's own sort — otherwise the pin could not unify with
            // the obligation body anyway.
            let Some(Some(clause_sort)) = clause_sorts.get(&subject) else { continue };
            let Some(place_sort) = crate::place_sort(func, place) else { continue };
            if &place_sort != clause_sort {
                continue;
            }
            // Recorded BEFORE the liveness gate, so a pin the gate suppresses is
            // VISIBLE to the caller's tripwire instead of silently weakening the VC.
            required.insert(subject.clone());
            // (2) LIVENESS: the defining statement's own token must be exactly the
            // token the obligation body's read of `subject` carries. Any later
            // write, havoc, or inter-block join moves the body's token and
            // suppresses the pin.
            let Some(use_tok) = sv.version_token_at(func, use_block.id, use_point, &subject) else {
                continue;
            };
            if !use_tok
                .strip_prefix('s')
                .and_then(|s| s.split_once('_'))
                .is_some_and(|(b_str, k_str)| {
                    (b_str == "0" || !b_str.starts_with('0'))
                        && (k_str == "0" || !k_str.starts_with('0'))
                        && b_str.parse::<usize>().ok() == Some(def_block.id.0)
                        && k_str.parse::<usize>().ok() == Some(k)
                })
            {
                continue;
            }
            // (1) VALUE FROM THE BODY: the statement's own rvalue, with its reads
            // taken at the read-point `k` (values BEFORE this write).
            let Ok(value) = crate::chc::rvalue_to_formula(func, rvalue) else { continue };
            let value = version_rename_owned_at(value, sv, func, def_block.id, k);
            // Trust (2026-09-30, stale-read seal): reads still bare at `k` would be
            // re-stamped by a later whole-formula rename; seal them, or emit no pin
            // (the ledger below then fails the row closed).
            let Some(value) = seal_bare_reads(sv, func, def_block.id, k, value) else { continue };
            let versioned = format!("{subject}#{use_tok}");
            if !pinned.insert(versioned.clone()) {
                continue;
            }
            let pin =
                Formula::Eq(Box::new(Formula::var_owned(versioned, place_sort)), Box::new(value));
            formula = Formula::And(vec![pin, formula]);
            pinned_bases.insert(subject);
        }
    }
    // The ledger's residue: clause-mentioned places the body writes but this lane
    // left unconstrained. Sorted for a deterministic diagnostic.
    let mut unpinned: Vec<String> =
        required.into_iter().filter(|s| !pinned_bases.contains(s)).collect();
    unpinned.sort();
    (formula, unpinned)
}

/// Does a transitive-return-pin rvalue name a WHOLE LOCAL that one of the scanned
/// blocks assigns?
///
/// This is the scope gate for the one-more-hop re-conjoin at the transitive return
/// pin. It answers the only question that matters there: did the pin just introduce
/// a name whose VALUE lives in a block definition that the relevance filter has
/// already run past?
///
///   * `Var("_8")` where the arm does `_8 = x / 2` — YES. The pin says
///     `_0 == _8` and nothing else in the formula says what `_8` is.
///   * `Var("_5.0")`, the checked-arithmetic value field — NO. Not a whole local,
///     and the arm's assert-passed semantic guard already pins it.
///   * `Var("_1")`, a parameter read — NO. No statement assigns it, so there is
///     no block definition to recover and the entry facts already ground it.
///   * a constant — NO free variables at all.
///
/// Whole-local only, by exact `_<digits>` spelling: a projected or derived name
/// (`_5.0`, `x*`, `s__slice_len`) is grounded by a different lane, and widening
/// this gate to them would perturb formulas that are already correct.
fn transitive_pin_names_locally_defined_local(
    rformula: &Formula,
    scan_blocks: &[&trust_types::BasicBlock],
) -> bool {
    trust_types::any_free_variable_name(rformula, &mut |name| {
        let Some(rest) = name.strip_prefix('_') else {
            return false;
        };
        if rest.is_empty() || !rest.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        }
        let Ok(local) = rest.parse::<usize>() else {
            return false;
        };
        scan_blocks.iter().any(|b| {
            b.stmts.iter().any(|stmt| {
                matches!(stmt, Statement::Assign { place, .. }
                    if place.local == local && place.projections.is_empty())
            })
        })
    })
}

/// Whether every value `rvalue` reads is unchanged from its statement to the
/// return point along `path` (each block with the index of its first statement
/// still to run; a block's terminator runs too). A whole local must not be
/// written on the path nor mutably borrowed anywhere in `func` (an alias could
/// write it unseen); a read through a `Deref` additionally rules out any store
/// through a pointer, `Unlocatable` write, call or drop on the path. An rvalue
/// whose reads are not enumerated here answers `false`.
fn return_pin_reads_are_current(
    func: &VerifiableFunction,
    path: &[(&trust_types::BasicBlock, usize)],
    window: &[&trust_types::BasicBlock],
    rvalue: &Rvalue,
) -> bool {
    fn operand_place(operand: &Operand) -> Option<&Place> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            _ => None,
        }
    }
    let mut places = Vec::new();
    match rvalue {
        Rvalue::Use(a) | Rvalue::UnaryOp(_, a) | Rvalue::Cast(a, _) => {
            if let Some(p) = operand_place(a) {
                places.push(p);
            } else if !matches!(a, Operand::Constant(_)) {
                return false;
            }
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => {
            for op in [a, b] {
                if let Some(p) = operand_place(op) {
                    places.push(p);
                } else if !matches!(op, Operand::Constant(_)) {
                    return false;
                }
            }
        }
        Rvalue::Aggregate(_, operands) => {
            places.reserve(operands.len());
            for op in operands {
                if let Some(p) = operand_place(op) {
                    places.push(p);
                } else if !matches!(op, Operand::Constant(_)) {
                    return false;
                }
            }
        }
        _ => return false,
    }
    let reads_through_pointer =
        places.iter().any(|p| p.projections.iter().any(|q| matches!(q, Projection::Deref)));
    // Review round 44: the pin is conjoined with BARE names, and a bare PARAMETER
    // name is its ENTRY value. After `s.0 += 1`, the bare `s.0` read by `_0 = copy
    // s.0` named the entry field and contradicted the versioned pin of the same
    // return, so `ensures result == 12345` was vacuously proved and certified. A
    // parameter read is admitted only when the body never writes it, and a read
    // through a pointer is refused (its pointee has no such guarantee).
    if reads_through_pointer {
        return false;
    }
    let mut locals: Vec<usize> = places.iter().map(|p| p.local).collect();
    locals.sort_unstable();
    locals.dedup();
    for (block, from) in path {
        for stmt in block.stmts.iter().skip(*from) {
            if locals.iter().any(|&local| {
                !matches!(stmt.local_write(local), trust_types::LocalWrite::Untouched)
            }) {
                return false;
            }
            if reads_through_pointer {
                let pointer_store = match stmt {
                    Statement::Assign { place, .. }
                    | Statement::SetDiscriminant { place, .. }
                    | Statement::Deinit { place } => {
                        place.projections.iter().any(|q| matches!(q, Projection::Deref))
                    }
                    _ => false,
                };
                if pointer_store
                    || matches!(stmt.local_write(usize::MAX), trust_types::LocalWrite::Unlocatable)
                {
                    return false;
                }
            }
        }
        if locals.iter().any(|&local| {
            !matches!(block.terminator.local_write(local), trust_types::LocalWrite::Untouched)
        }) {
            return false;
        }
        if reads_through_pointer
            && !matches!(
                block.terminator,
                Terminator::Goto(_)
                    | Terminator::SwitchInt { .. }
                    | Terminator::Return
                    | Terminator::Assert { .. }
            )
        {
            return false;
        }
    }
    // Review round 45: the block defs of every `window` block are conjoined with the
    // pin, and they name a local written in the window by VERSION, and READ it bare
    // as its value entering the block, while the pin names it BARE as its value at
    // the return. `let mut c = x; c += 1; c` pinned `_0` to both `c`'s pre- and
    // post-write versions (a vacuous proof), and `c = x; side(); c = c + 1; c` (the
    // first write in an ANCESTOR) pinned the stale `c`. A read local with two or more
    // writes among the window and every block that can reach it is refused; one write
    // is the only value this path gives it (a later one is refused above), and a
    // single-assignment local has one value everywhere.
    if locals.iter().any(|&local| {
        !crate::local_defs::is_single_static_assignment(func, local)
            && ((1..=func.body.arg_count).contains(&local)
                || local_writes_reaching(func, window, local) > 1)
    }) {
        return false;
    }
    if locals.iter().any(|&local| {
        crate::any_local_write_stmt(func, &func.body.blocks, local, |_block, stmt| {
            crate::stmt_escapes_local(func, stmt, local)
        })
    }) {
        return false;
    }
    true
}

/// Whether `rvalue` has an operand that is neither a place read nor a constant (an
/// `Operand::Unsupported` the encoder cannot lower).
fn rvalue_has_unlowerable_operand(rvalue: &Rvalue) -> bool {
    let is_unlowerable = |operand: &Operand| {
        !matches!(operand, Operand::Copy(_) | Operand::Move(_) | Operand::Constant(_))
    };
    match rvalue {
        Rvalue::Use(a) | Rvalue::UnaryOp(_, a) | Rvalue::Cast(a, _) => is_unlowerable(a),
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => is_unlowerable(a) || is_unlowerable(b),
        Rvalue::Aggregate(_, operands) => operands.iter().any(is_unlowerable),
        _ => false,
    }
}

/// The most writes of `local` any single execution path makes through `window`
/// (in order; the last block holds the pin) and the blocks before it: the window's
/// own writes plus the heaviest predecessor chain into its first block. Sibling
/// arms that merge before the window count once, not summed; a cycle on the way
/// counts as two (review round 45: a value pinned under a bare name must be the
/// only one the path gives it; see [`return_pin_reads_are_current`]).
fn local_writes_reaching(
    func: &VerifiableFunction,
    window: &[&trust_types::BasicBlock],
    local: usize,
) -> usize {
    fn writes_in(block: &trust_types::BasicBlock, local: usize) -> usize {
        block
            .stmts
            .iter()
            .filter(|stmt| !matches!(stmt.local_write(local), trust_types::LocalWrite::Untouched))
            .count()
            + usize::from(!matches!(
                block.terminator.local_write(local),
                trust_types::LocalWrite::Untouched
            ))
    }
    fn heaviest_into(
        func: &VerifiableFunction,
        v2_preds: &crate::fn_memo::V2Predecessors,
        target: usize,
        local: usize,
        memo: &mut FxHashMap<usize, usize>,
        on_stack: &mut Vec<usize>,
    ) -> usize {
        if let Some(&known) = memo.get(&target) {
            return known;
        }
        if on_stack.contains(&target) {
            return 2;
        }
        on_stack.push(target);
        let mut best = 0;
        v2_preds.for_each_predecessor(func, BlockId(target), |pred| {
            let through = writes_in(pred, local)
                + heaviest_into(func, v2_preds, pred.id.0, local, memo, on_stack);
            best = best.max(through);
            if best >= 2 {
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        });
        on_stack.pop();
        let best = best.min(2);
        memo.insert(target, best);
        best
    }
    let Some(first) = window.first() else { return 0 };
    let own: usize = window.iter().map(|b| writes_in(b, local)).sum();
    if own >= 2 {
        return own;
    }
    let v2_preds = crate::fn_memo::v2_predecessors_or_build(func);
    let mut memo = FxHashMap::default();
    own + heaviest_into(func, &v2_preds, first.id.0, local, &mut memo, &mut Vec::new())
}

/// Re-read a raw `ensures` text copy with extraction's admitted length rebinding:
/// `xs__len` becomes `xs__slice_len` ONLY for a base whose canonical leaf already
/// occurs in `func.postconditions` (extraction rebound it there under the
/// `requires` admission, `rebind_postcondition_lengths`). Any other `__len` leaf is
/// left as written.
fn rebind_text_lengths(func: &VerifiableFunction, mut parsed: Formula) -> Formula {
    if func.postconditions.is_empty()
        || !trust_types::any_formula_node(&parsed, &mut |node| {
            node.var_name().is_some_and(|name| name.ends_with("__len"))
        })
    {
        return parsed;
    }
    let mut rebindings = Vec::new();
    trust_types::for_each_free_variable_name(&parsed, &mut |name| {
        if let Some(base) = name.strip_suffix("__len") {
            let canonical = format!("{base}__slice_len");
            if func
                .postconditions
                .iter()
                .any(|f| trust_types::any_free_variable_name(f, &mut |v| v == canonical))
            {
                rebindings.push((name.to_string(), canonical));
            }
        }
    });
    rebindings.sort();
    rebindings.dedup();
    for (name, canonical) in rebindings {
        parsed = parsed.rename_var(&name, &canonical);
    }
    parsed
}
