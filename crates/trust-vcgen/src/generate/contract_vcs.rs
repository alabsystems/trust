// Contract obligations: `requires`/`ensures` clauses turned into VCs, and the
// return-slot pinning that makes a postcondition mentioning the return value
// refer to the value actually returned on each path.

use super::*;

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
    let guard_paths_map = v2_build_path_guard_map(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let path_definition_map = v2_build_path_definition_map(func);
    let semantic_guards = match summaries {
        Some(s) => build_semantic_guard_map_with_summaries(func, s),
        None => build_semantic_guard_map(func),
    };
    let may_reassigned = v2_may_reassigned_per_block(func);
    let empty_kill: FxHashSet<String> = FxHashSet::default();
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
    let mut seen_posts: Vec<Formula> = func.postconditions.clone();
    let mut posts: Vec<(Formula, String, SourceSpan, Option<usize>)> = func
        .postconditions
        .iter()
        .map(|f| {
            (
                f.clone(),
                format!("{f:?}"),
                func.span.clone(),
                unique_source_contract_index_for_formula(func, ContractKind::Ensures, f),
            )
        })
        .collect();
    for (contract_index, contract) in func.contracts.iter().enumerate() {
        if !matches!(contract.kind, ContractKind::Ensures) {
            continue;
        }
        let body = contract
            .body
            .strip_prefix(contracts::LOWERED_CONTRACT_PREFIX)
            .unwrap_or(&contract.body);
        // Sort-exact equality here made every `bool` clause fail to recognize
        // its own typed lowering, appending a SECOND, ill-sorted copy of the
        // same postcondition. That copy cannot lower to typed TrustIr, so it
        // carries no `trust.vc.formula.payload` and lands as a fail-closed
        // Unknown that also denies the whole function native evidence. Match
        // modulo the parser's `Sort::Int` sentinel so the typed clause — the
        // type-faithful reading, and the one that actually gets solved — is
        // recognized as already present.
        if let Some(parsed) = trust_types::parse_spec_expr(body)
            && !seen_posts.iter().any(|f| parsed_clause_matches_typed(&parsed, f))
        {
            seen_posts.push(parsed.clone());
            posts.push((parsed, body.to_string(), contract.span.clone(), Some(contract_index)));
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
    // `_0`, never `_0_discr`/`_0_value*`, so `Not(post)` stays satisfiable by
    // havoc REGARDLESS of the body and the obligation is reported Failed with a
    // counterexample MINTED over the under-constrained encoding — not a program
    // trace. Such a postcondition must land as the fail-closed NON-REFUTABLE
    // Unknown (below), never as a refutable per-return-block VC, and never be
    // silently dropped (a false-PROVE).
    // Names the body-aware lane can now GROUND (Option/Result-return
    // `_0_discr` — plus `_0_value` for an integer payload — when every return
    // path pins them in-body; empty otherwise — see
    // `enum_return_grounded_model_vars`). Subtracting these from the per-post
    // ungrounded set lets an Option<integer>/Result postcondition survive into
    // `explicit_postconditions` so it reaches the pin loop's discr/value pins,
    // instead of being shunted to fail-closed Unknown. Compared on BASE name
    // (strip any `#version` token) since the return-slot terms are unversioned.
    let groundable = enum_return_grounded_model_vars(func);
    // Len-witness lane (b62): payload-component length pairs whose equality every
    // return path establishes in-body. The same resolver supplies the pins below.
    let len_pairs = len_witness_credited_pairs(func, &posts);
    let len_groundable: FxHashSet<String> =
        len_pairs.iter().flat_map(|(a, b)| [a.name.clone(), b.name.clone()]).collect();
    // Ordering/sign-witness lane (b62 F4), likewise gated across every return path.
    let ord_items = ordering_witness_credited_items(func, &posts);
    let ord_groundable: FxHashSet<String> =
        ord_items.iter().flat_map(OrdWitnessItem::model_names).collect();
    let mut explicit_postconditions: Vec<(Formula, Option<usize>, bool)> = Vec::new();
    let mut ungrounded_posts: Vec<(Vec<String>, String, SourceSpan, Option<usize>)> = Vec::new();
    for (post, origin, span, source_contract_index) in posts {
        // An arithmetic-bearing clause the Machine{w} lane admits
        // (`machine_faithful_clause_admissible`: one shared declared machine
        // width, wrap-exact fragment, no spec `/`/`%`) enters the refutable
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
                let ungrounded = contracts::ungrounded_spec_model_vars(&post);
                if ungrounded.is_empty() {
                    explicit_postconditions.push((post, source_contract_index, true));
                } else {
                    ungrounded_posts.push((ungrounded, origin, span, source_contract_index));
                }
                continue;
            }
            if !parsed_source_clause_matches(func, ContractKind::Ensures, &post) {
                let ungrounded = contracts::ungrounded_spec_model_vars(&post);
                if ungrounded.is_empty() {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        span,
                        "formula-only ensures uses unmodeled fixed-width machine arithmetic",
                        &origin,
                        contract_metadata_with_source_index(
                            contract_metadata,
                            source_contract_index,
                        ),
                    ));
                } else {
                    ungrounded_posts.push((
                        ungrounded,
                        origin,
                        span,
                        source_contract_index,
                    ));
                }
            }
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
            ungrounded_posts.push((ungrounded, origin, span, source_contract_index));
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

    for block in &func.body.blocks {
        if !matches!(block.terminator, Terminator::Return) {
            continue;
        }

        let predecessors: Vec<&trust_types::BasicBlock> = func
            .body
            .blocks
            .iter()
            .filter(|pred| v2_terminator_targets(&pred.terminator).contains(&block.id))
            .collect();
        let vc_blocks: Vec<&trust_types::BasicBlock> =
            if predecessors.is_empty() { vec![block] } else { predecessors };

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

        for (post, source_contract_index, machine_lane) in &explicit_postconditions {
            let clause_metadata =
                contract_metadata_with_source_index(contract_metadata, *source_contract_index);
            // SOUNDNESS (P0, hunt-6): a postcondition over a REASSIGNED by-value parameter would
            // be proved against the parameter's FINAL value, not its `ensures` ENTRY snapshot — a
            // false proof (`#[ensures(move |r| *r==a)] fn f(mut a){ a+=1; a }`: VC checks r==a_final
            // = 11==11 PROVED, true r==a_entry = 11==10 FALSE). Fail-close: emit ONE not-proved
            // Postcondition VC (a SATisfiable `Bool(true)` is never UNSAT, so it is reported
            // not-proved, NEVER PROVED) until entry-snapshot modeling lands. (FULL is already sound.)
            if postcondition_references_mutated_param(func, post) {
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
                        &Formula::Not(Box::new(post.clone())),
                    ) {
                        Some(machine) => machine,
                        None => {
                            vcs.push(contracts::spec_unverifiable_vc(
                                func,
                                func.span.clone(),
                                "machine-arithmetic ensures over a reassigned parameter is outside the declared-width fragment",
                                &format!("{post:?}"),
                                clause_metadata,
                            ));
                            continue;
                        }
                    }
                } else {
                    Formula::Not(Box::new(post.clone()))
                };
                vcs.push(VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: func.name.as_str().into(),
                    location: func.span.clone(),
                    formula,
                    contract_metadata: clause_metadata,
                    obligation: None,
                });
                continue;
            }
            // Re-sort the postcond's return variable `_0` to the real return sort.
            let post = substitute_summary_params(
                post,
                &[("_0".to_string(), Formula::var_owned("_0".to_string(), ret_sort.clone()))],
            );
            for vc_block in &vc_blocks {
                let mut formula = Formula::Not(Box::new(post.clone()));
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
                let mut unlowerable_return_assignment = false;
                for def_block in [&**vc_block, block] {
                    for stmt in &def_block.stmts {
                        let Statement::Assign { place, rvalue, .. } = stmt else {
                            continue;
                        };
                        if place.local != 0 || !place.projections.is_empty() {
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
                        // bypasses the relevance filter. Sound: `_0` is the return
                        // slot, assigned once before `Return`.
                        match crate::chc::rvalue_to_formula(func, rvalue) {
                            Ok(rformula) => {
                                let sort = crate::place_sort(func, place).unwrap_or(Sort::Int);
                                let ret_def = Formula::Eq(
                                    Box::new(Formula::var_owned(
                                        format!("_{}", place.local),
                                        sort,
                                    )),
                                    Box::new(rformula),
                                );
                                formula = Formula::And(vec![ret_def, formula]);
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
                            Err(_) => unlowerable_return_assignment = true,
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
                                    if let Ok(field_formula) =
                                        crate::chc::operand_to_formula_checked(func, op)
                                    {
                                        // Pin under the RAW `_<local>.<i>` name the
                                        // contract parser mints (`Var("_0.0")`), NOT
                                        // the `place_to_var_name` alias `__ret.<i>`
                                        // (local 0 carries source name `__ret`) — just
                                        // as the scalar pin above uses raw `_<local>`.
                                        // Otherwise the pin and the postcondition name
                                        // distinct field vars and never connect.
                                        let field_name = format!("_{}.{}", place.local, i);
                                        let field_sort = crate::place_sort(func, &field_place)
                                            .unwrap_or(Sort::Int);
                                        let field_def = Formula::Eq(
                                            Box::new(Formula::var_owned(field_name, field_sort)),
                                            Box::new(field_formula),
                                        );
                                        formula = Formula::And(vec![field_def, formula]);
                                    }
                                }
                            }
                        }
                    }
                }

                // Trust (OUT-PARAMETER pin): a postcondition over a place written
                // THROUGH a `&mut` PARAMETER (`ensures *x == 0`, `ensures self.n
                // == 0`) had NO antecedent at all and was decided by havoc.
                //
                // The block-def extraction DOES produce the fact
                // (`Eq(Var("x*"), Int(0))` for `(*_1) = 0`), but
                // `version_block_def_at_establish` cannot stamp it: it looks for
                // the establish point of the `*`-STRIPPED base (`x`), and a `&mut`
                // PARAMETER is never assigned in-body, so `block_def_establish_stmt`
                // returns `None` and the fact is left BARE. Meanwhile the
                // obligation body IS versioned (`x*#s0_0`), so the bare fact is
                // name-disjoint and `combine_relevant_block_defs` prunes it as
                // irrelevant. The VC collapses to `Not(Eq(Var("x*#s0_0"), Int(0)))`
                // — a query about a free variable, which the solver "refutes"
                // regardless of the body. TRUE and FALSE twins came back
                // identically Failed.
                //
                // Pin it explicitly here, exactly as the return slot above is
                // pinned for the same reason ("block-def extraction does not
                // surface a `_0 = Use(..)` ... so `_0` stays havoc'd").
                let (with_pins, unpinned_out_params) =
                    with_out_param_pins(func, &sv, block, &[vc_block, &block], &post, formula);
                formula = with_pins;

                // Trust (Option/Result-return discriminant/value pin): ground the
                // synthetic spec-model terms `_0_discr` / `_0_value` that the
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
                // but must pin `_0_discr==1`, the parser's `is_ok ⟹ _0_discr!=0`;
                // `Err` is variant 1 and pins `_0_discr==0`). Pinning the raw
                // index for Result would swap `is_ok`/`is_err` polarity — a
                // simultaneous false-PROVE and false-FAIL. Pin at MOST ONE
                // discriminant per return path (last / nearest-to-return wins) so
                // two differing-variant assignments can never conjoin
                // `_0_discr==0 ∧ _0_discr==1` into a vacuous UNSAT (a
                // false-PROVE). SOUND: `_0 = Some(x)` / `_0 = Ok(x)` literally
                // carries its variant and payload x, so `_0_discr==<model> ∧
                // _0_value==x` are exact identities of the constructed value under
                // the parser's reading; `_0 = None` / `_0 = Err(e)` is
                // `_0_discr==0` exactly — a FALSE postcondition still refutes
                // (every term pinned to its genuine value, never credited).
                // `_0_value` is pinned only on the payload variant's path
                // (`Some`/`Ok`) with an integer payload; leaving it free on the
                // other path — and on non-integer payloads (ny-cert's Rat/Vec
                // shapes, whose `_0_value*` terms the gate keeps UNGROUNDED so
                // they never reach this refutable lane) — is sound (a free var
                // only adds SAT/refute, never manufactures UNSAT/proof).
                let enum_return_pin =
                    resolve_enum_return_aggregate(func, *vc_block, block).map(|(kind, variant, ops)| {
                        // Parser-convention model discriminant (Result INVERTED).
                        let discr = std_enum_model_discr(kind, variant);
                        let payload = if variant == std_enum_payload_variant(kind)
                            && ops.len() == 1
                            && crate::operand_ty_cow(func, &ops[0])
                                .as_deref()
                                .is_some_and(|t| matches!(t, Ty::Int { .. }))
                        {
                            crate::chc::operand_to_formula_checked(func, &ops[0]).ok()
                        } else {
                            None
                        };
                        (discr, payload)
                    });
                if let Some((discr, payload)) = enum_return_pin {
                    let discr_def = Formula::Eq(
                        Box::new(Formula::var_owned("_0_discr".to_string(), Sort::Int)),
                        Box::new(Formula::Int(discr)),
                    );
                    formula = Formula::And(vec![discr_def, formula]);
                    if let Some(pf) = payload {
                        let value_def = Formula::Eq(
                            Box::new(Formula::var_owned("_0_value".to_string(), Sort::Int)),
                            Box::new(pf),
                        );
                        formula = Formula::And(vec![value_def, formula]);
                    }
                }

                // Trust (len-witness pin, b62): ground the CREDITED payload-
                // component length pairs (`_0_value.<i>.<j>_len` — the lowered
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
                for pair in &len_pairs {
                    if let Some(pins) = len_witness_path_pins(func, *vc_block, block, pair) {
                        for pin in pins {
                            formula = Formula::And(vec![pin, formula]);
                        }
                    }
                }

                // Trust (ordering/sign-witness pin, b62 F4): ground the
                // CREDITED `__trust_ok` pair / `_0_value_sign` terms (the
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
                    if let Some(pins) = ordering_witness_path_pins(func, *vc_block, block, item) {
                        for pin in pins {
                            formula = Formula::And(vec![pin, formula]);
                        }
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
                for term_block in [&**vc_block, block] {
                    // Any exact-value MODELED call (saturating_add/sub, wrapping_neg)
                    // whose dest is the return slot. Its value is an `Ite`; a term-
                    // `Ite` in a postcondition obligation is pruned by trust-mc / not
                    // routed by trust-wp, so `_0 == <Ite>` stays UNKNOWN. `ite_free_equality`
                    // LIFTS the `Ite` to formula-level guards, which both backends
                    // discharge — so `#[ensures]` over `x.saturating_add(y)` /
                    // `x.wrapping_neg()` proves. See `ite_free_equality`.
                    let modeled = saturating_call_dest_value(func, &term_block.terminator)
                        .or_else(|| wrapping_neg_call_dest_value(func, &term_block.terminator));
                    if let Some((dest, value)) = modeled
                        && dest.local == 0
                        && dest.projections.is_empty()
                    {
                        let sort = crate::place_sort(func, &Place::local(0)).unwrap_or(Sort::Int);
                        let pin =
                            ite_free_equality(&Formula::var_owned("_0".to_string(), sort), &value);
                        formula = Formula::And(vec![pin, formula]);
                    }
                }

                // Trust (clamp/min/max return pin, over-refutation audit #8): when a
                // predecessor's TERMINATOR is an integer std `Ord::min`/`max`/`clamp`
                // call whose dest IS the return slot `_0` (the function returns the
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
                    if let Terminator::Call { func: callee, args, dest, target: Some(_), .. } =
                        &term_block.terminator
                        && dest.local == 0
                        && dest.projections.is_empty()
                        && is_single_static_assignment(func, dest.local)
                    {
                        let ret_var = Formula::var_owned("_0".to_string(), ret_sort.clone());
                        for fact in ord_min_max_clamp_result_facts(func, callee, args, &ret_var) {
                            formula = Formula::And(vec![fact, formula]);
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
                let return_src_local: Option<usize> =
                    scan_blocks.iter().flat_map(|b| b.stmts.iter().rev()).find_map(|stmt| {
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
                                Some(p.local)
                            }
                            _ => None,
                        }
                    });
                if let Some(src) = return_src_local {
                    let arm_def =
                        scan_blocks.iter().flat_map(|b| b.stmts.iter().rev()).find_map(|stmt| {
                            let Statement::Assign { place, rvalue, .. } = stmt else {
                                return None;
                            };
                            if place.local != src || !place.projections.is_empty() {
                                return None;
                            }
                            if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
                                return None;
                            }
                            crate::chc::rvalue_to_formula(func, rvalue).ok()
                        });
                    if let Some(rformula) = arm_def {
                        let sort = crate::place_sort(func, &Place::local(0)).unwrap_or(Sort::Int);
                        let pin_ret = Formula::Eq(
                            Box::new(Formula::var_owned("_0".to_string(), sort.clone())),
                            Box::new(rformula.clone()),
                        );
                        let pin_src = Formula::Eq(
                            Box::new(Formula::var_owned(format!("_{src}"), sort)),
                            Box::new(rformula),
                        );
                        formula = Formula::And(vec![pin_ret, pin_src, formula]);
                    }
                }

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
                if returns_via_deref_load(block)
                    || (vc_block.id != block.id && returns_via_deref_load(vc_block))
                {
                    formula = v2_formula_with_block_defs(func, block, formula);
                    if vc_block.id != block.id {
                        formula = v2_formula_with_block_defs(func, vc_block, formula);
                    }
                }

                if let Some(path_defs) = path_definition_map.get(&vc_block.id)
                    && !path_defs.is_empty()
                {
                    let mut live = v2_live_path_defs(func, vc_block, path_defs);
                    // soundness (round-11): v2_live_path_defs only sees
                    // STATEMENT-level redefs, so a fact the block's TERMINATOR
                    // invalidates (a `Call` dest such as `_0`, or a `&mut`/`&raw
                    // mut` pointee escaping into the call) would survive into the
                    // postcondition VC and vacuously discharge it. Drop those here,
                    // mirroring the fixpoint outflow kill. Monotone-sound.
                    let term_defs: FxHashSet<String> =
                        terminator_def_names(func, vc_block).into_iter().collect();
                    if !term_defs.is_empty() {
                        live.retain(|f| formula_survives_redefs(f, &term_defs));
                    }
                    if !live.is_empty() {
                        let mut conjuncts = live;
                        conjuncts.push(formula);
                        formula = Formula::And(conjuncts);
                    }
                }

                // Trust S2c (exemption): path + semantic guards conjoined AFTER the
                // rename (moved below), exempt from it.
                {
                    // Trust: P-B — unconditional rename (see the v2 lane). Required
                    // so an establish-versioned threaded fact connects to its LIVE
                    // postcondition-lane successor read; verdict-preserving with
                    // empty preconditions.
                    let killed = may_reassigned.get(&vc_block.id).unwrap_or(&empty_kill);
                    formula = conjoin_preconditions_versioned(
                        func,
                        vc_block.id,
                        &func.preconditions,
                        killed,
                        formula,
                    );
                }
                if let Some(block_guard_paths) = guard_paths_map.get(&vc_block.id) {
                    formula = v2_formula_with_path_guards(func, &sv, block_guard_paths, formula);
                }
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
                if !sem_conjuncts.is_empty() {
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
                if ret_alias != "_0" {
                    formula = substitute_summary_params(
                        &formula,
                        &[(
                            ret_alias.clone(),
                            Formula::var_owned("_0".to_string(), ret_sort.clone()),
                        )],
                    );
                }

                // Trust (return-slot version unification): vcgen versions the negated
                // postcondition's `_0` at the Return point, where `_0` carries the MERGED
                // reaching-set token of all return predecessors (e.g. `_0#s1_0_s6_0`),
                // while the return-value pin this lane conjoined (`Eq(_0#s6_0, <retval>)`)
                // carries the SINGLE establish-point token of THIS predecessor's write.
                // The two names denote the SAME final return value on this per-predecessor
                // Return-block VC but do not unify, so the negated postcondition stays
                // havoc'd and a valid bound (`retval >= step`) is vacuously SAT (fails
                // closed as-emitted). Unify the return slot's versions to the pin's version
                // so the linear chain `step <= retval = _0 < step` contradicts and
                // `certify_violation` discharges. Version-aware, scoped to the return slot
                // ONLY and to THIS one VC — see `unify_return_slot_versions`.
                formula = unify_return_slot_versions(formula);

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
                let global_facts = build_global_invariant_facts(func);
                if !global_facts.is_empty() {
                    let mut with_facts = global_facts;
                    with_facts.push(formula);
                    formula = Formula::And(with_facts);
                }

                // Trust (branchy #[ensures] over-refutation fix, 2026-07-04):
                // `unify_return_slot_versions` only fires when the return slot has a
                // SINGLE pin version; a MULTI-RETURN body (`if c { a } else { a }`)
                // pins `_0` under two distinct reaching-def tokens (bare `_0` from
                // one predecessor's block-def, `_0#s3_0` from the return block's
                // merged-token read), so it bails and the negated postcondition
                // stays disconnected from the return value — FALSE-REFUTING a valid
                // branchy postcondition (`ensures |r| *r >= a` over `if a<100 {a}
                // else {a}` is UNSAT-to-violate yet was refuted). The return slot
                // `_0` is single-static-assignment (assigned once, before `Return`),
                // so collapsing its version tokens to the bare name is an IDENTITY on
                // the formula's meaning (the same argument the safety lane relies on
                // — see `normalize_ssa_version_tokens`) that CONNECTS the two pins:
                // `_0 == __ret#s1_0 == a` and `_0 == __ret#s1_0_s2_0` then unify so
                // `¬(_0 >= a)` becomes `¬(a >= a)` = UNSAT = proved. SOUND in the
                // false-PROOF direction too: a REASSIGNED-parameter postcondition
                // already fail-closed above (`postcondition_references_mutated_param`),
                // and a NON-SSA local keeps its load-bearing token disjointness
                // (normalize only collapses genuinely single-assignment locals), so
                // this never credits a violated postcondition.
                formula = normalize_ssa_version_tokens(func, &formula);

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
                    && !formula_has_return_slot_pin(&formula)
                    && !formula_has_complete_return_projection_pins(&formula, &post)
                    && formula_references_return_slot(&post)
                {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        v2_block_span(func, vc_block),
                        "return assignment is outside the encoder fragment and no conjunct pins the return slot; refusing a refutable query over a free return value",
                        &format!("{post:?}"),
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
                let unconstrained_out_param = unpinned_out_params.iter().find(|subject| {
                    let versioned = match sv.version_token_at(
                        func,
                        block.id,
                        block.stmts.len(),
                        subject,
                    ) {
                        Some(tok) => format!("{subject}#{tok}"),
                        None => (*subject).clone(),
                    };
                    !formula_pins_var_name(&formula, &versioned)
                });
                if let Some(subject) = unconstrained_out_param {
                    vcs.push(contracts::spec_unverifiable_vc(
                        func,
                        v2_block_span(func, vc_block),
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

                // Machine{w} lane: the clause was admitted CONDITIONALLY on the
                // fully assembled VC — negated clause, block defs, return pins,
                // versioned hypotheses, guards — translating wholesale into
                // declared-width QF_BV (ratified L1 rule 4). The mathematical-Int
                // spelling assembled above reads machine arithmetic unbounded —
                // the confirmed `result + 1 > result` false-proof vector — so it
                // must NEVER be emitted for such a clause: on any conjunct
                // outside the fragment (mixed body widths, collection facts) the
                // row falls closed to the visible unsupported shape instead.
                if *machine_lane {
                    match contracts::machine_faithful_vc_formula(func, &formula) {
                        Some(machine) => formula = machine,
                        None => {
                            vcs.push(contracts::spec_unverifiable_vc(
                                func,
                                v2_block_span(func, vc_block),
                                "machine-arithmetic ensures conjoined body facts outside the declared-width fragment",
                                &format!("{post:?}"),
                                clause_metadata,
                            ));
                            continue;
                        }
                    }
                }

                // (Term-`Ite` elimination is applied UNIFORMLY to every VC — this
                // postcondition included — by the central normalization loop in
                // `generate_vcs_impl`, so it is not repeated here.)

                vcs.push(VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: func.name.as_str().into(),
                    location: v2_block_span(func, vc_block),
                    formula,
                    contract_metadata: clause_metadata,
                    obligation: None,
                });
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
    // The one and only relaxation, and only on a variable leaf.
    if let (Some((parsed_name, parsed_sort)), Some((typed_name, typed_sort))) =
        (formula_var_leaf(parsed), formula_var_leaf(typed))
    {
        return parsed_name == typed_name
            && (parsed_sort == typed_sort || *parsed_sort == Sort::Int);
    }
    // Identical constructor and identical non-formula payload, then identical
    // children pairwise.
    if !same_formula_shape(parsed, typed) {
        return false;
    }
    let parsed_children = parsed.children();
    let typed_children = typed.children();
    parsed_children.len() == typed_children.len()
        && parsed_children
            .iter()
            .zip(typed_children.iter())
            .all(|(p, t)| parsed_clause_matches_typed(p, t))
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
        Formula::Eq(lhs, _) => matches!(&**lhs, Formula::Var(n, _) if n == name),
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
        let mut found = false;
        formula.visit(&mut |node| {
            if let Formula::Var(name, _) = node {
                found |= name.starts_with("__trust_unsupported_operand_")
                    || name == "__unknown_operand";
            }
        });
        found
    }

    let mut references_whole_slot = false;
    let mut required: FxHashSet<String> = FxHashSet::default();
    postcondition.visit(&mut |node| {
        if let Formula::Var(name, _) = node {
            let base = name.split('#').next().unwrap_or(name);
            if base == "_0" {
                references_whole_slot = true;
            } else if base.starts_with("_0.") {
                required.insert(base.to_string());
            }
        }
    });
    if references_whole_slot || required.is_empty() {
        return false;
    }

    fn collect_positive_projection_pins(formula: &Formula, pins: &mut FxHashSet<String>) {
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
                        pins.insert(base.to_string());
                    }
                }
            }
            _ => {}
        }
    }

    let mut pinned: FxHashSet<String> = FxHashSet::default();
    collect_positive_projection_pins(formula, &mut pinned);
    required.is_subset(&pinned)
}

/// Whether a clause formula references the return slot (`_0`, a versioned
/// `_0#<tok>`, or a projected `_0.<field>` spelling) anywhere.
pub(super) fn formula_references_return_slot(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |node| {
        if let Formula::Var(name, _) = node {
            let base = name.split('#').next().unwrap_or(name);
            found |= base == "_0" || base.starts_with("_0.");
        }
    });
    found
}

/// The UNIQUE return-slot version (`_0` / `_0#<tok>`) appearing as the LHS of an
/// `Eq` — i.e. the return-value pin `Eq(_0#<v>, <retval>)` the postcondition lane
/// conjoined for this Return-block VC. `None` when there is no such pin, or more
/// than one distinct version (ambiguous — leave the formula untouched rather than
/// risk unifying to a non-final version, so we never over-unify unsoundly).
pub(super) fn return_slot_pin_version(formula: &Formula) -> Option<String> {
    let mut pins: FxHashSet<String> = FxHashSet::default();
    formula.visit(&mut |f| {
        if let Formula::Eq(l, _) = f
            && let Formula::Var(n, _) = &**l
            && is_return_slot_name(n)
        {
            pins.insert(n.clone());
        }
    });
    if pins.len() == 1 { pins.into_iter().next() } else { None }
}

/// Within a SINGLE per-predecessor Return-block Postcondition VC, unify every
/// statement-version of the return slot `_0` (`_0` / `_0#<tok>`) to the version the
/// return-value pin uses.
///
/// vcgen versions the negated postcondition's `_0` at the Return point, where `_0`
/// carries the MERGED reaching-set token of all return predecessors (e.g.
/// `_0#s1_0_s6_0` from `version_token_at`'s inter-block reaching set), while the
/// return-value pin this lane conjoined (`Eq(_0#s6_0, <retval>)`) carries the SINGLE
/// establish-point token of THIS predecessor's write. The two names denote the SAME
/// final return value on this per-predecessor VC but do not unify, so the negated
/// postcondition stays havoc'd and a valid bound is vacuously SAT.
///
/// SOUNDNESS: `_0` (RETURN_PLACE) is assigned before `Return`, so within one
/// per-predecessor Return-block VC every surviving `_0#*` denotes local 0's single
/// final value — unifying them equates only provably-equal names. Scoped to the
/// return slot ONLY (never another local, via `is_return_slot_name`) and to THIS one
/// VC (never across blocks), so it cannot make a FALSE postcondition provable: the
/// FALSE `result > step` control still fails closed because `retval == step` stays
/// satisfiable after unification. Unifies ONLY when the pin gives a UNIQUE version;
/// an ambiguous or absent pin leaves the formula unchanged (no unsound over-unify).
pub(super) fn unify_return_slot_versions(formula: Formula) -> Formula {
    let Some(target) = return_slot_pin_version(&formula) else {
        return formula;
    };
    let mut out = formula.clone();
    for v in formula.free_variables() {
        if v != target && is_return_slot_name(&v) {
            out = out.rename_var(&v, &target);
        }
    }
    out
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

/// Collect `(name, sort)` for every `Var` in `formula`.
fn formula_var_sorts(formula: &Formula) -> Vec<(String, Sort)> {
    let mut out: Vec<(String, Sort)> = Vec::new();
    let _ = formula.clone().map(&mut |node| {
        if let Formula::Var(name, sort) = &node {
            out.push((name.clone(), sort.clone()));
        }
        node
    });
    out
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
    let mut decls = func.body.locals.iter().filter(|d| d.index == place.local);
    let Some(decl) = decls.next() else { return false };
    // A duplicated declaration index makes the type ambiguous; refuse.
    if decls.next().is_some() {
        return false;
    }
    matches!(decl.ty, Ty::Ref { mutable: true, .. })
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
    post: &Formula,
    mut formula: Formula,
) -> (Formula, Vec<String>) {
    // Sorts the CLAUSE uses, keyed by base (unversioned) name. A name the clause
    // spells at two different sorts is ambiguous and gets no pin.
    let mut clause_sorts: FxHashMap<String, Option<Sort>> = FxHashMap::default();
    for (name, sort) in formula_var_sorts(post) {
        let base = name.split('#').next().unwrap_or(&name).to_string();
        clause_sorts
            .entry(base)
            .and_modify(|slot| {
                if slot.as_ref() != Some(&sort) {
                    *slot = None;
                }
            })
            .or_insert(Some(sort));
    }
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
            if use_tok != format!("s{}_{k}", def_block.id.0) {
                continue;
            }
            // (1) VALUE FROM THE BODY: the statement's own rvalue, with its reads
            // taken at the read-point `k` (values BEFORE this write).
            let Ok(value) = crate::chc::rvalue_to_formula(func, rvalue) else { continue };
            let value = version_rename_at(&value, sv, func, def_block.id, k);
            let versioned = format!("{subject}#{use_tok}");
            if !pinned.insert(versioned.clone()) {
                continue;
            }
            let pin = Formula::Eq(
                Box::new(Formula::var_owned(versioned, place_sort)),
                Box::new(value),
            );
            formula = Formula::And(vec![pin, formula]);
            pinned_bases.insert(subject.clone());
        }
    }
    // The ledger's residue: clause-mentioned places the body writes but this lane
    // left unconstrained. Sorted for a deterministic diagnostic.
    let mut unpinned: Vec<String> =
        required.into_iter().filter(|s| !pinned_bases.contains(s)).collect();
    unpinned.sort();
    (formula, unpinned)
}
