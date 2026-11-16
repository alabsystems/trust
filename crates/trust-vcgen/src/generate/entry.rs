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
    // T3 C07, C08s: the rows join a fresh context of their own, which drops here, through
    // the row oracle at the generation's sink (`super::row_sink`), so every row this entry
    // returns has been read back from a context and compared with itself in every field.
    // The eager rows are returned, so the list is the one generated. T3 C08: no Spine is
    // formed for a context no one reads (`Spines::Skip`, L4-C08-6).
    //
    // PERF-COMPILER-VCGEN-809: that context is dropped unread, and a disagreement only
    // re-interns the eager row, which is returned either way, so the oracle here is
    // unobservable in the result. MEASURED with `vcgen_fixture_bench`: interning plus
    // the read-back comparison (`push_checked_row`) was 27% of `generate_vcs`. It stays
    // on in debug builds (every test that calls this entry keeps exercising the
    // interner and the oracle), and an optimized build skips it. A caller that READS
    // the context (`generate_vcs_rows`, the production R1 harvest) keeps it always.
    #[cfg(debug_assertions)]
    {
        let mut own = trust_types::vc_context::VcContext::new();
        generate_vcs_in_own_frame(func, Some(&mut own), super::recipes::Spines::Skip)
    }
    #[cfg(not(debug_assertions))]
    {
        generate_vcs_in_own_frame(func, None, super::recipes::Spines::Skip)
    }
}

/// [`generate_vcs`] into the caller's context `rows` (T3 C07p, design D-VC-1): every row is
/// interned through the row oracle as it joins the generation's sink (T3 C08s), a block-def
/// row as a Spine row where the sink can join it as one (T3 C08, `super::recipes`), and the
/// eager rows are returned, as every `_rows` producer returns them, so the list is the one
/// generated. A generation the work meter refused after its lanes ran leaves the rows that
/// joined before the refusal in `rows`, beside its one refusal row.
pub fn generate_vcs_rows(
    func: &VerifiableFunction,
    rows: &mut trust_types::vc_context::VcContext,
) -> Vec<VerificationCondition> {
    generate_vcs_in_own_frame(func, Some(rows), super::recipes::Spines::Join)
}

/// The generation [`generate_vcs`] and [`generate_vcs_rows`] share: [`generate_vcs_impl`]
/// in a frame of its own, its rows written into `rows`, its block-def rows as Spine rows
/// as `spines` says.
fn generate_vcs_in_own_frame(
    func: &VerifiableFunction,
    rows: Option<&mut trust_types::vc_context::VcContext>,
    spines: super::recipes::Spines,
) -> Vec<VerificationCondition> {
    // Trust (ALLOC-STRIDE-ADT-2, ARGS-FINGERPRINT-READ-1 round 4): a fresh frame of
    // the SAME function keeps the compiler's element-size binding and its
    // `DefId`-decided self-call blocks (regeneration parity); nothing else crosses.
    let context = crate::VcgenContext::for_function_inheriting_regeneration_facts(&func.def_path);
    crate::with_function_vcgen_context(&func.def_path, &context, || {
        let none = FxHashSet::default();
        generate_vcs_impl_with_origins(func, None, false, &none, KeepOrigins::No, rows, spines).vcs
    })
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
    let strips_pre =
        |pre: &Formula| contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre);
    // Trust (formula-only symmetry, 2026-09-25): ENSURES ONLY, and the asymmetry is the
    // whole soundness argument.
    //
    // A retained POSTcondition is a GOAL. `generate_v2_contract_vcs_impl` translates it
    // wholesale into declared-width QF_BV or fails closed with a visible
    // `spec_unverifiable_vc`, so the `Formula::Add` the unmodeled filter exists to stop
    // never reaches a solver as unbounded `Int` — `machine_faithful_clause_admissible`
    // IS that translation, called for its `is_some()`. That is why it may admit
    // `_0 == a + b`: what gets emitted is `bvadd` at the declared width.
    //
    // A retained PRECONDITION is a PREMISE, and has NO paired translation gate. Measured
    // before this landed: retaining one put `Ge(Sub(d, 1), 0)` into a
    // `LoopInvariantInitiation` row as live Int arithmetic over a `u8`, which is a
    // false PROVE. Preconditions therefore keep the unconditional strip.
    //
    // The two edits (this one and the `standalone_unmodeled_contract_rows` guard) land
    // TOGETHER or not at all: with this one alone an admitted clause gets BOTH a
    // refutable `Postcondition` row and a contradicting `SpecUnverifiable`, which the
    // source-side pin "an admitted clause does not also keep a fail-closed row" forbids.
    let strips_post = |post: &Formula| {
        contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, post)
            && !contracts::machine_faithful_clause_admissible(func, post)
    };
    // Trust (INTRINSIC-RESIDUAL-1, 2026-10-08): this is the ONE view every ordinary
    // body lane reads `func.preconditions` through, so it is also where the 128-bit
    // parameter type-range facts no producer attaches are supplied — see
    // `missing_param_type_range_facts`. The top-level entries already applied
    // `with_param_type_range_facts` before their analysis memo, so this is empty
    // there; it is what keeps the entries that call this view directly (the E4/E5
    // regeneration paths, the per-lane helpers) reading the same hypothesis.
    let missing_ranges = missing_param_type_range_facts(func);
    let first_pre = (!func.preconditions.is_empty())
        .then(|| func.preconditions.iter().position(strips_pre))
        .flatten();
    let first_post = (!func.postconditions.is_empty())
        .then(|| func.postconditions.iter().position(strips_post))
        .flatten();
    if missing_ranges.is_empty() && first_pre.is_none() && first_post.is_none() {
        return std::borrow::Cow::Borrowed(func);
    }
    let mut sanitized = func.clone();
    if let Some(first_idx) = first_pre {
        let mut idx = 0usize;
        sanitized.preconditions.retain(|pre| {
            let i = idx;
            idx += 1;
            if i < first_idx {
                true
            } else if i == first_idx {
                false
            } else {
                !strips_pre(pre)
            }
        });
    }
    if let Some(first_idx) = first_post {
        let mut idx = 0usize;
        sanitized.postconditions.retain(|post| {
            let i = idx;
            idx += 1;
            if i < first_idx {
                true
            } else if i == first_idx {
                false
            } else {
                !strips_post(post)
            }
        });
    }
    sanitized.preconditions.extend(missing_ranges);
    std::borrow::Cow::Owned(sanitized)
}

/// The type-range facts of the 128-bit integer PARAMETERS — the widths the
/// extractor's envelope leaves out — that `func.preconditions` does not already
/// carry: `And([Ge(p, MIN_T), Le(p, MAX_T)])` for every NAMED `i128`/`u128`
/// parameter, over the parameter's formula name ([`crate::local_var_name`]), with
/// the bounds spelled by [`crate::range::type_min_formula`] /
/// [`crate::range::type_max_formula`] (`u128::MAX` is `Formula::UInt`, the one
/// bound `Formula::Int` cannot hold; the arithmetic batteries already state it so).
///
/// THE GAP THIS CLOSES (INTRINSIC-RESIDUAL-1, measured 2026-10-08). Outside the
/// arithmetic batteries (`conjoin_arg_type_ranges`), every lane — the postcondition
/// lane included — reads a parameter's range from ONE place, the entry hypothesis
/// `func.preconditions`, and only the extractor puts it there. The extractor's
/// `integer_param_range_preconditions` stops at width 64 (its bounds are
/// `Formula::Int` literals, and the exact recognizers that certify its facts as type
/// tautologies — `bmc_reduction::is_integer_param_range_fact`,
/// `trust_ir_bridge::member_precondition_is_integer_param_type_range`,
/// `trust_clean`'s `is_parameter_type_range_fact` — refuse 128-bit bounds). So every
/// `i128`/`u128` parameter reached those lanes unbounded on `Sort::Int`, and the
/// solver refuted TRUE clauses with values no execution can hold: over captures of
/// the stage-2 trustc (`tests/fixtures/range_adversarial/wide_ok_*`), `ensures
/// result >= 0` for `fn f(x: u128) -> u128 { x }` was `Failed` with `x = -1`, and
/// `x <= i128::MAX` for an `i128` was `Failed` with `x = 2^127`; that compiler
/// reported the `i128` rows `postcond FAILED, verified_counterexample = true`
/// against correct code. The range is a property of the parameter's DECLARED TYPE,
/// so the generator states it for the widths no producer does.
///
/// Widths `1..=64` stay the PRODUCER's: a body without the extractor's facts at those
/// widths (a stale capture, a body built in code) gets nothing here. Stating them too
/// would change the formulas the trust-ir spine must byte-match and the
/// certification-shape pins in trust-ir-bridge / trust-clean / trust-router, which all
/// build on bodies without the facts (measured 2026-10-07: 28 + 5 + 1 tests), so that
/// move is a cross-crate decision, pinned by
/// `tests/counterexample_type_range_guard.rs`. At 128 bits no producer states a fact
/// and no such pin exists, so nothing is duplicated and nothing is contradicted.
///
/// IDEMPOTENT: a fact already carried is not added again. The L0 safety block lane
/// conjoins [`producer_preconditions`] instead — it bounds parameters itself.
///
/// SOUNDNESS. Each fact is a tautology of the parameter's type: rustc type-checks
/// every actual into the range and a reassignment preserves the type, so it holds at
/// entry and at every later point — the argument the extractor's own doc makes, and
/// the one `conjoin_arg_type_ranges` makes for the arithmetic lanes. A true premise
/// can only delete models no execution produces; a real violation's witness respects
/// the same range and still refutes.
///
/// NOT FOR A DELIBERATELY EMPTIED HYPOTHESIS. An empty `preconditions` is also what a
/// caller builds on purpose when it asks an UNCONDITIONAL question of a clone — the
/// inferred-return check (`inferred_return_check_vcs`), the TINV arm-lemma probe, the
/// L0 callsite replay of a callee without its `requires`. Those run under
/// [`without_stated_param_ranges`], which makes this return nothing, so their rows
/// stay exactly what they were.
pub(crate) fn missing_param_type_range_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if STATED_PARAM_RANGES_SUSPENDED.with(std::cell::Cell::get) {
        return Vec::new();
    }
    let mut missing = Vec::new();
    for fact in wide_param_type_range_facts(func) {
        if !func.preconditions.contains(&fact) && !missing.contains(&fact) {
            missing.push(fact);
        }
    }
    missing
}

/// Every type-range fact [`missing_param_type_range_facts`] can state for `func` —
/// one per named 128-bit integer parameter — whether or not it is carried yet.
fn wide_param_type_range_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::body_has_wide_int_param_for(func) {
        return Vec::new();
    }
    let locals_slice = if func
        .body
        .locals
        .get(func.body.arg_count)
        .is_some_and(|d| d.index == func.body.arg_count)
        && func.body.locals[..=func.body.arg_count]
            .iter()
            .enumerate()
            .all(|(i, d)| d.index == i)
    {
        &func.body.locals[1..=func.body.arg_count]
    } else {
        &func.body.locals[..]
    };
    let mut facts = Vec::new();
    for decl in locals_slice {
        if decl.index < 1 || decl.index > func.body.arg_count || decl.name.is_none() {
            continue;
        }
        let Ty::Int { width, signed } = &decl.ty else {
            continue;
        };
        let (width, signed) = (*width, *signed);
        // The extractor's envelope is `1..=64`; past 128 there is no integer type.
        if width <= 64 || width > 128 {
            continue;
        }
        let name = crate::local_var_name(func, decl);
        let var = Formula::Var(name, Sort::Int);
        facts.push(Formula::And(vec![
            Formula::Ge(Box::new(var.clone()), Box::new(crate::range::type_min_formula(width, signed))),
            Formula::Le(Box::new(var), Box::new(crate::range::type_max_formula(width, signed))),
        ]));
    }
    facts
}

/// `func.preconditions` WITHOUT the generator's 128-bit parameter facts — what the
/// producer attached. The L0 safety block lane conjoins this, not the view's list.
///
/// That lane needs no stated range: it bounds every integer parameter by its type
/// itself (`conjoin_arg_type_ranges`, 128-bit included), and its bitvector encodings
/// (the signed-128 add/sub/neg overflow rows) range over exactly the type's values,
/// so the facts would only add a disconnected duplicate. They would also break the
/// trust-ir spine's byte-equal reconstruction of those rows, which conjoins
/// `func.preconditions` as the producer wrote them (`trust-ir-bridge`'s
/// `signed_128_bv_overflow_parity_tests`, measured red with the facts in), and the
/// spine cannot read this view (trust-vcgen is only a dev-dependency there). If the
/// extractor ever states 128-bit facts itself, this filter and the generator's
/// statement go together.
pub(crate) fn producer_preconditions(func: &VerifiableFunction) -> Vec<Formula> {
    if func.preconditions.is_empty() {
        return Vec::new();
    }
    let stated = wide_param_type_range_facts(func);
    if stated.is_empty() {
        return func.preconditions.clone();
    }
    func.preconditions.iter().filter(|pre| !stated.contains(pre)).cloned().collect()
}

/// `func` with [`missing_param_type_range_facts`] appended to its entry hypothesis.
/// No clone is made when nothing is missing — every body without a named 128-bit
/// integer parameter.
///
/// The top-level entries apply this right after placing opaque values and BEFORE
/// entering their analysis memo, so every lane, the memo and the discharge pass see
/// one view (the same discipline as `with_placed_opaque_values`).
pub(crate) fn with_param_type_range_facts(
    func: &VerifiableFunction,
) -> std::borrow::Cow<'_, VerifiableFunction> {
    let missing = missing_param_type_range_facts(func);
    if missing.is_empty() {
        return std::borrow::Cow::Borrowed(func);
    }
    let mut ranged = func.clone();
    ranged.preconditions.extend(missing);
    std::borrow::Cow::Owned(ranged)
}

thread_local! {
    /// Set only inside [`without_stated_param_ranges`].
    static STATED_PARAM_RANGES_SUSPENDED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Run `generate` with the generator's own parameter type-range statement suspended:
/// [`missing_param_type_range_facts`] answers nothing inside it, on this thread.
///
/// For a caller that EMPTIED `preconditions` on purpose to ask an unconditional
/// question of a clone (see that function's doc). Such a caller decided what its rows
/// assume, and its rows must not change under it: the inferred-return check and the
/// arm lemma feed Clean-kernel certification, and the L0 replay re-imposes the
/// caller's own constraints. Suspending can only WITHHOLD true facts, so it cannot
/// make anything provable; it restores the previous state on exit, including on
/// unwind.
pub(crate) fn without_stated_param_ranges<R>(generate: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            STATED_PARAM_RANGES_SUSPENDED.with(|suspended| suspended.set(self.0));
        }
    }
    let _restore = Restore(STATED_PARAM_RANGES_SUSPENDED.with(|suspended| suspended.replace(true)));
    generate()
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
    let _input_analysis_scope = super::FuncAnalysisScope::enter_if_unbound(func);
    crate::validate_function(func).ok()?;

    let _gen_work_scope = crate::gen_work_scope();
    let tail_call_expanded = super::with_tail_calls_expanded_cached(func);
    let semantic_func = tail_call_expanded.as_ref();
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(semantic_func);
    let arithmetic_safe_func = arithmetic_safe_func.as_ref();
    let _analysis_scope = super::FuncAnalysisScope::enter_if_unbound(arithmetic_safe_func);
    // Generate the row from the exact shared TailCall semantic view so an E4
    // candidate sealed to that view remains usable. `generate_loop_decreases_vc`
    // does not consume function pre/postcondition assumptions. Only the interval
    // environment does, and that continues to use the production-sanitized view
    // below. Passing the sanitized clone into row generation would look like body
    // drift to the fresh-context candidate and unnecessarily disable feedback.
    let raw =
        contracts::regenerate_loop_decreases_with_invariant_feedback_vcs(semantic_func, feedback);
    let merged_env = abstract_interp::merged_interval_environment(arithmetic_safe_func);
    let augmented = abstract_interp::augment_batch(&raw, &merged_env);
    if crate::gen_work_tripped() {
        return None;
    }
    Some((raw, augmented))
}

/// [`regenerate_loop_decreases_with_invariant_feedback_production_variants`] into the
/// caller's context `rows`, the body's (T3 C07p, design D-VC-1): both batches are interned
/// through the row oracle after the generation's work scope has closed, and returned as
/// generated. A regenerated row equal to a row already in `rows` is the same node there.
#[must_use]
pub fn regenerate_loop_decreases_with_invariant_feedback_production_variants_rows(
    func: &VerifiableFunction,
    feedback: &[contracts::LoopInvariantFeedbackCandidate],
    rows: &mut trust_types::vc_context::VcContext,
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    let (raw, augmented) =
        regenerate_loop_decreases_with_invariant_feedback_production_variants(func, feedback)?;
    intern_eager_rows(rows, raw.iter().chain(&augmented));
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
    let _input_analysis_scope = super::FuncAnalysisScope::enter_if_unbound(func);
    crate::validate_function(func).ok()?;

    let _gen_work_scope = crate::gen_work_scope();
    let tail_call_expanded = super::with_tail_calls_expanded_cached(func);
    let semantic_func = tail_call_expanded.as_ref();
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(semantic_func);
    let arithmetic_safe_func = arithmetic_safe_func.as_ref();
    let _analysis_scope = super::FuncAnalysisScope::enter_if_unbound(arithmetic_safe_func);

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
        contracts::regenerate_loop_decreases_with_invariant_feedback_vcs(semantic_func, feedback)
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

/// Reconstruct exact scalar source domains and all original type premises for
/// a bounded Boolean body. Nominal enum formals are checked through the shared
/// enum entry model and deliberately receive no scalar source binder. This
/// relation conveys no proof authority; complete VC/callee certificates remain
/// independently required. Unknown or extra premises fail closed.
#[must_use]
pub fn boolean_source_entry_domains(
    function: &VerifiableFunction,
    callees: Option<&[crate::InferredReturnCall]>,
) -> Option<std::collections::BTreeMap<String, trust_types::CompilerContractValueDomain>> {
    (function.body.return_ty == Ty::Bool)
        .then(|| scalar_return_source_entry_domains(function, callees))
        .flatten()
}

/// The shared entry-domain relation for Boolean and fixed-width unsigned
/// scalar returns. Unsigned bodies pass the existing scalar return evaluator;
/// their source consumers still check every original clause and body row.
/// Inferred call inputs convey no proof authority and must independently replay.
#[must_use]
pub fn scalar_return_source_entry_domains(
    function: &VerifiableFunction,
    callees: Option<&[crate::InferredReturnCall]>,
) -> Option<std::collections::BTreeMap<String, trust_types::CompilerContractValueDomain>> {
    super::inferred_return::with_inferred_return_calls(function, callees.unwrap_or(&[]), || {
        super::source_entry::domains(function)
    })
    .ok()
    .flatten()
}

/// Reconstruct source-bound postcondition violations and typed body declines
/// in both production spellings. This is semantic data, not proof authority:
/// a consumer must require an exact, complete raw/interval-augmented row bijection before
/// binding an authored clause to these formulas.
///
/// Callee-summary-dependent rows deliberately decline that match when the
/// summary-free reconstruction differs. A partial generation is never a
/// complete source-clause formula.
#[must_use]
pub fn regenerate_postcondition_production_variants(
    func: &VerifiableFunction,
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    let context = crate::VcgenContext::for_function_inheriting_regeneration_facts(&func.def_path);
    crate::with_function_vcgen_context(&func.def_path, &context, || {
        regenerate_postcondition_variants_in_context(func, false)
    })
}

/// Candidate-only reconstruction with explicitly supplied typed callee inputs.
/// These inputs convey no proof authority; consumers must independently check
/// their original-body certificates before spending the resulting relation.
pub fn regenerate_postcondition_production_variants_with_inferred_calls(
    func: &VerifiableFunction,
    callees: &[crate::InferredReturnCall],
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    super::inferred_return::with_inferred_return_calls(func, callees, || {
        regenerate_postcondition_variants_in_context(func, true)
    })
    .ok()
    .flatten()
}

fn regenerate_postcondition_variants_in_context(
    func: &VerifiableFunction,
    use_inferred_calls: bool,
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    let _input_analysis_scope = super::FuncAnalysisScope::enter_if_unbound(func);
    crate::validate_function(func).ok()?;
    let _gen_work_scope = crate::gen_work_scope();
    let placed = super::with_placed_opaque_values_cached(func);
    let ranged = with_param_type_range_facts(placed.as_ref());
    let expanded = super::with_tail_calls_expanded_cached(ranged.as_ref());
    let sanitized = without_unmodeled_contract_arithmetic(expanded.as_ref());
    let semantic = sanitized.as_ref();
    let _analysis_scope = super::FuncAnalysisScope::enter_if_unbound(semantic);
    if crate::memory_image_vc(semantic).is_some() || func_exceeds_vcgen_budget(semantic) {
        return None;
    }
    let _write_sets = callee_write_set::enter_callee_write_sets(None);
    let summaries = if use_inferred_calls {
        let has_calls = super::terminator_presence_for(semantic).has_call;
        let summaries = super::inferred_return::calls::database(semantic);
        if has_calls && summaries.is_none() {
            return None;
        }
        summaries
    } else {
        None
    };
    // Reconstruct the final production row, not the contract lane's input to
    // it. In particular, inferred Boolean return equations contain term ITEs;
    // the shared sink lifts those and applies the same SSA/havoc/refusal passes
    // that the original compiler row received. Never normalize supplied rows.
    let mut sink = RowSink::new(semantic, None);
    sink.lane(generate_v2_contract_vcs_impl(semantic, summaries.as_ref()));
    if crate::gen_work_tripped() {
        return None;
    }
    let raw = sink
        .finish()
        .vcs
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition | VcKind::DeclinedContractBody(_)))
        .collect::<Vec<_>>();
    let merged_env = abstract_interp::merged_interval_environment(semantic);
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
    let _input_analysis_scope = super::FuncAnalysisScope::enter_if_unbound(func);
    crate::validate_function(func).ok()?;

    let _gen_work_scope = crate::gen_work_scope();
    let tail_call_expanded = super::with_tail_calls_expanded_cached(func);
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(tail_call_expanded.as_ref());
    let arithmetic_safe_func = arithmetic_safe_func.as_ref();
    let _analysis_scope = super::FuncAnalysisScope::enter_if_unbound(arithmetic_safe_func);

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
pub(super) fn standalone_unmodeled_contract_rows(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    if func.preconditions.is_empty() && func.postconditions.is_empty() {
        return Vec::new();
    }
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
            // Ensures only — see `without_unmodeled_contract_arithmetic`. A `requires`
            // of the same shape keeps its disclosure, because it is a premise nothing
            // translates.
            if contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, formula)
                && !(matches!(kind, ContractKind::Ensures)
                    && contracts::machine_faithful_clause_admissible(func, formula))
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

/// [`generate_vcs_with_extra_precondition`] into the caller's context `rows` (T3 C07p):
/// as [`generate_vcs_rows`], over `func` with `extra` conjoined.
pub fn generate_vcs_with_extra_precondition_rows(
    func: &VerifiableFunction,
    extra: &Formula,
    rows: &mut trust_types::vc_context::VcContext,
) -> Vec<VerificationCondition> {
    let mut f = func.clone();
    f.preconditions.push(extra.clone());
    generate_vcs_rows(&f, rows)
}

/// Summary-aware [`generate_vcs`]: body safety VCs may soundly assume proved
/// callee postconditions (separate-compilation boundary). `None` is byte-identical
/// to [`generate_vcs`]; only the v2 safety lane consults the summaries.
pub(crate) fn generate_vcs_with_summaries(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> Vec<VerificationCondition> {
    let context = crate::VcgenContext::for_function_inheriting_regeneration_facts(&func.def_path);
    crate::with_vcgen_context(&context, || {
        generate_vcs_impl(func, Some(summaries), false, &FxHashSet::default())
    })
}

pub(super) fn generate_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
    hardened: bool,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
) -> Vec<VerificationCondition> {
    generate_vcs_impl_with_origins(
        func,
        summaries,
        hardened,
        box_deref_ops,
        KeepOrigins::No,
        None,
        super::recipes::Spines::Skip,
    )
    .vcs
}

/// [`generate_vcs_impl`], keeping the safety walk's origin block beside each of its
/// rows (T3 C05, `super::overflow_origins`) when `keep` says so, and writing every row into
/// `rows` through the row oracle when the caller keeps a context (T3 C08s), its block-def
/// rows as Spine rows when `spines` says so (T3 C08, `super::recipes`).
///
/// Every row joins the generation's sink (`super::row_sink`) as its lane returns it, and
/// the sink runs the per-row passes on it there. The origins are aligned with the sink's
/// rows by index; the sink's sort and its unsafe-row splice move them with the rows, and
/// `overflow_origins_tests`' census holds every use of the sink here to one whose phase
/// the sink checks.
pub(super) fn generate_vcs_impl_with_origins(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
    hardened: bool,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    keep: KeepOrigins,
    rows: Option<&mut trust_types::vc_context::VcContext>,
    spines: super::recipes::Spines,
) -> SinkOutput {
    // OPAQUE-SCALAR-ID-1 / OPAQUE-REF-ID-1: every unmodeled carrier (opaque scalar,
    // opaque reference, unsupported operand) must carry its identity before any
    // lane names it. Extracted and deserialized bodies already do (no clone); a
    // body built in code is placed here, ahead of the analysis memo below.
    let _input_analysis_scope = super::FuncAnalysisScope::enter_if_unbound(func);
    let placed = super::with_placed_opaque_values_cached(func);
    let func = placed.as_ref();
    // INTRINSIC-RESIDUAL-1: the 128-bit integer parameters' type ranges, which the
    // extractor does not attach (no clone for a body without such a parameter). Also
    // ahead of the analysis memo, so the memo keys on the view every lane reads.
    let ranged = with_param_type_range_facts(func);
    let func = ranged.as_ref();
    // Trust (verifier-perf, MEASURED 2026-08-31): every VC lane below rebuilds
    // the SAME two whole-CFG analyses of `func` at every obligation point —
    // `StmtVersionCtx::build` (two dataflow fixpoints) and the path-guard walk.
    // On `trust-spec-elab` that was >=99.7% of the compile: `elab_term` (815
    // basic blocks) never reached a report at all. One memo for the whole
    // per-function generation; the scope holds a shared borrow of `func`, so the
    // memo provably cannot observe a mutation. See `FuncAnalysisScope`.
    let analysis_scope_func = func;
    let _analysis_scope = super::FuncAnalysisScope::enter_placed_if_unbound(func);
    if let Some(vc) = crate::memory_image_vc(func) {
        return SinkOutput::single(rows, vc);
    }
    if let Err(error) = crate::validate_function(func) {
        return SinkOutput::single(rows, malformed_trust_ir_vc(func, &error));
    }
    // T3 C08: the block-def builders record their combinations while the generation
    // writes into its caller's context, so the sink can join those rows as Spine rows
    // (`recipes`).
    let _recipes =
        super::recipes::RecipeScope::open(rows.is_some() && spines == super::recipes::Spines::Join);

    // One semantic projection closes the legacy-consumer surface for MIR
    // `TailCall`: every established call, unsafe/FFI, atomic, dataflow, and
    // per-Return postcondition lane sees the equivalent ordinary call writing
    // local 0 followed by a fresh Return block.  The source model itself stays
    // unchanged, so exact E5/source identity and serialization retain the real
    // TailCall terminator.  See `VerifiableFunction::with_tail_calls_expanded`.
    //
    // The projection does NOT keep frame lifetime: its `Call` reads as if this frame
    // outlived the callee, which a `become` does not. Each consumer below that
    // credits a call with this frame's storage takes the source's tail-call blocks
    // (ids the projection keeps) and judges the projected call there as the tail
    // call it is (`sep_engine::terminator_ends_frame`; REVIEW-A4C4-MINORS-1): the sep
    // engine's addr_of confinement and modeled-call rows
    // (`check_sep_unsafe_blocked_ops`) and the FFI buffer-extent facts
    // (`ffi_buffer_extent::call_facts`).
    let tail_call_blocks = sep_engine::tail_call_blocks(func);
    let tail_call_expanded = super::with_tail_calls_expanded_cached(func);
    let func = tail_call_expanded.as_ref();

    // verifier-perf: enter the mid-generation work-meter scope. On the OUTERMOST entry
    // this resets the per-function type-clone work counter; the guard (held for this
    // call) keeps it scoped so a nested entry shares one budget. If the cumulative clone
    // work crosses the budget mid-walk, the meter trips, `place_ty` hands back cheap
    // fail-closed leaves, and the post-gen check below discards this whole function.
    // SOUNDNESS: DROP-ONLY — see `crate::place_ty` / `gen_work`.
    let _gen_work_scope = crate::gen_work_scope();

    // Trust (BLOCKER 2 — callee effect summaries): install the MIR-derived callee
    // write-sets for the whole obligation walk. `summaries = None` (every legacy
    // entry, including the bare `generate_vcs`) installs an EMPTY map, which is
    // byte-identical to the pre-existing conservative call havoc — the refinement
    // exists only where a callee's own extracted body proves it.
    let _write_sets = callee_write_set::enter_callee_write_sets(summaries);

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
        let vc = unsupported_mir_vc(
            func,
            "TrustVcGenBudgetExceeded".to_string(),
            format!(
                "function `{}` exceeds the VC-generation budget (recursive-datatype \
                 aggregate explosion); its obligations are left Unknown (fail-closed) to \
                 keep the rest of the crate verifiable",
                func.name
            ),
            func.span.clone(),
        );
        return SinkOutput::single(rows, vc);
    }

    let standalone_contract_rows = standalone_unmodeled_contract_rows(func);
    // One sanitized view feeds every ordinary body lane below.  Raw authored
    // contract strings are deliberately retained for explicit Unknown rows.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    let _inner_analysis_scope =
        (!std::ptr::eq(func, analysis_scope_func)).then(|| super::FuncAnalysisScope::enter(func));

    // Canonical path — generate real overflow/divzero VCs so that integration
    // tests calling `trust_vcgen::generate_vcs` (e.g. `real_ay_verification`,
    // `m5_e2e_loop`) receive meaningful VCs. The old checker modules were
    // migrated to trust-bmc; the
    // upstream MirRouter dispatches at a higher layer, but callers that still
    // invoke this function directly need safety VCs with real SMT formulas,
    // not an empty Vec.
    //
    // T3 C05: the walk pairs each row with its origin block, and the pairing is kept
    // (`origins`) for the proven-overflow-check elision seam's join table, together
    // with whether the walk was cut short.
    let walk = generate_v2_safety_vcs_impl_with_origins_checked(func, summaries);
    // The walk's row cap latches no budget, so the compiler's checkpoint never sees it:
    // refuse here, as the work-meter trip below does. A prefix of a function's rows is
    // not its obligation set; published as one it could report the function proved
    // with obligations never posed.
    //
    // SOUNDNESS: DROP-ONLY. `UnsupportedMir` preclassifies to Unknown, never Proved.
    if walk.row_capped {
        let vc = unsupported_mir_vc(
            func,
            "TrustVcGenRowCapExceeded".to_string(),
            format!(
                "function `{}` generated more than {} safety rows; its obligations are left \
                 Unknown (fail-closed), since a prefix of them is not its obligation set",
                func.name,
                super::safety::MAX_VC_ROWS_PER_FUNCTION,
            ),
            func.span.clone(),
        );
        return SinkOutput::single(rows, vc);
    }
    // T3 C08s: every row joins the generation's sink as its lane returns it, the walk's
    // first, and the sink runs the per-row passes on it there (`super::row_sink`).
    let mut sink = RowSink::new(func, rows);
    sink.walk(walk, keep);

    // Bounds/rvalue lane is also summary-aware so `arr[parse(i)]` can be discharged
    // from `parse`'s postcondition (not just overflow/divzero).
    sink.lane(generate_v2_rvalue_safety_vcs_impl(func, summaries));

    // Trust (#nia-oom): mechanically flag bulk heap allocations whose size is
    // not provably bounded — the class that let AY's NIA tableau grow to 203 GB
    // and OOM-kill the host. Discharged by a reaching bound/precondition or a
    // budget-checked allocator; fails closed otherwise.
    sink.lane(generate_unbounded_allocation_vcs(func));

    // Trust (unwrap panic-freedom, dominated-safe): solvable refutation VCs for
    // `unwrap`/`expect` calls whose receiver discriminant is pinned to the
    // success variant (guarded or by construction). Exactly the calls this lane
    // models are suppressed from the UnsupportedMir stream below (same
    // recognizer), so every known-panicking call yields exactly one obligation.
    sink.lane(generate_unwrap_panic_freedom_vcs(func));

    sink.lane(unsupported_mir_vcs(func));

    // Trust hardened profile: generate fail-closed obligations for OS/path,
    // byte/text, error-discard, panic, trust-domain, and compatibility hazards
    // that ordinary Rust type checking cannot prove away.
    // Trust (B2): `summaries` is threaded HERE too. It used to stop at the
    // per-statement lanes above, so the hardened panic-boundary twin — same
    // asserts, same blocks — could not see a proved callee's `ensures` and
    // refuted arithmetic the primary lane discharged. `targo trust check` turns
    // the `unix_hardened` profile on BY DEFAULT, so that gap was the production
    // behaviour while the profile-less UI fixtures stayed green.
    sink.lane(hardened::generate_hardened_vcs(func, hardened, summaries));

    // Deterministic ordering after parallel generation, by location. The origins move
    // with their rows (the same stable sort, so the rows' order is unchanged). Every
    // later lane appends.
    sink.sort_by_location();

    // Caller's OWN declared `ensures` lane is summary-aware so a function's contract
    // can be proved FROM its callees' contracts — the core separate-compilation case.
    sink.append(generate_v2_contract_vcs_impl(func, summaries));
    sink.append(standalone_contract_rows);

    // Termination checking via decreases clauses.
    // Appended through a list of its own, so the call cannot reach a row already in
    // the sink, whose origins ride beside it by index (T3 C05).
    let mut termination_rows = Vec::new();
    termination::check_termination(func, &mut termination_rows);
    sink.append(termination_rows);

    // COMPLETENESS: inline assembly is unconditionally unsafe and is otherwise
    // silently dropped (it extracts to an unmodeled `Terminator::Opaque`). Emit
    // its fail-closed obligation unconditionally — an asm-only function has no
    // other unsafe surface to trip `has_intrinsic_unsafe_surface` below.
    sink.append(unsafe_verify::detection::generate_inline_asm_vcs(func));

    // Unsafe-site coverage index for `check_unsafe` (which now runs AFTER the
    // separation engine, below): the `(block, MIR operation)` the engine was
    // interpreting for every `[unsafe:sep:*]` row it mints — never a span — plus
    // the blocks the path-guard walk reached. Empty is the fail-closed state —
    // every detected site keeps its stand-in row. See
    // `unsafe_verify::UnsafeCoverage` and `unsafe_verify::detection::decide_site`.
    let mut unsafe_coverage = unsafe_verify::UnsafeCoverage::default();
    // The unsafe-site rows are SPLICED back in at this position (see below), so
    // a row that survives this change keeps the exact ordinal it had before the
    // separation rows — ordinals feed obligation ids.
    let unsafe_rows_at = sink.mark();

    // THE SPLIT (2026-08-28). The separation engine used to run inside the SAME
    // `if` as `check_unsafe` above. That was wrong in both directions, because
    // `has_intrinsic_unsafe_surface` and the engine's own
    // `sep_engine::has_unsafe_patterns` do not admit the same set and neither is
    // a superset of the other (see that function's doc comment). The visible
    // symptom, measured: `g_noptr_and_box(w, flag)` minted ZERO
    // `[unsafe:sep:alloc]` rows while `e_rawptr_and_box(w, p: *const i64)` minted
    // FOUR PROVED ones — the two bodies differing only by an unused raw-pointer
    // parameter that is never dereferenced, merely `is_null()`-tested. The sep
    // row set was BODY-scoped when it must be SITE-scoped.
    //
    // Why the two halves must be gated SEPARATELY rather than by widening the
    // one gate: `check_unsafe`'s production output is a single always-`Bool(true)`
    // "[unsafe] missing SAFETY comment on unsafe block" row per detected unsafe
    // block (vcgen has no source map, so `comments` is always `&[]` and the
    // claim-bearing arms are unreachable — see
    // `unsafe_verify::detection::generate_safety_vcs`). That row is
    // UNDISCHARGEABLE BY CONSTRUCTION: `Bool(true)` is always SAT, and
    // `refute_unsafe_demand_findings` (rustc_mir_transform/trust_verify.rs)
    // additionally forces every `[unsafe`-marked row with a CONSTANT formula to
    // `Failed`. Widening the single gate to admit allocators would therefore have
    // charged an unprovable row to every body containing a `Box::new`.
    //
    // SOUNDNESS — this ADDS no proof and re-adds nothing unconditionally. The
    // rows still come from the UNCHANGED `check_sep_unsafe_blocked` path, which
    // re-derives them per CALL SITE by interpreting the body, and each carries a
    // real non-constant arithmetic formula (`ptr == 0`, or
    // `ptr != 0 ∧ ptr == 0` for an infallible box allocator whose abort-on-OOM
    // contract genuinely supplies the conjunct). A fallible allocator keeps the
    // bare SAT `ptr == 0` and still FAILS. And because the refute pass spares a
    // `Proved` result only when the formula is NOT `Formula::Bool(_)`, a row that
    // is merely admitted here can never be graded proved without a solver having
    // discharged a real predicate.
    //
    // ROW-MONOTONE: `check_sep_unsafe_blocked` already re-checks
    // `has_unsafe_patterns` internally and returns empty when it is false, so the
    // OLD effective condition was `has_intrinsic_unsafe_surface ∧
    // has_unsafe_patterns` and the NEW one is `has_unsafe_patterns` alone. That is
    // a strict weakening of a conjunction: no sep row that existed before can
    // disappear.
    if sep_engine::has_unsafe_patterns(func) {
        // Separation logic provenance engine — heap-aware VCs for
        // unsafe patterns (raw deref, alloc, dealloc, ptr::copy, transmute, etc.).
        // Each sep VC is conjoined with its block path DEFINITIONS and path GUARDS (the
        // same machinery the V2 VCs use; `SepFacts::wrap`) so a guarded unsafe op can be
        // discharged, and the unsafe-site coverage is told about the wrapped row.
        let sep_facts = SepFacts::for_function(func);
        for (vc, block_id, sep_op) in
            sep_engine::check_sep_unsafe_blocked_ops(func, &tail_call_blocks, box_deref_ops)
        {
            sink.append_sep(vc, &sep_facts, block_id, sep_op, &mut unsafe_coverage);
        }

        // NOTE: supersession of the always-`Bool(true)` "[unsafe] missing SAFETY
        // comment" row for a bounds-complete scalar-index `get_unchecked` is
        // performed at its SOURCE, per block, keyed on the block's own terminator
        // identity — which is WHY the split above is safe for it. That
        // supersession lives in `block_is_bounds_complete_unchecked_index`, inside
        // `generate_safety_vcs`, and so is unaffected by which `if` the sep engine
        // runs under: it never depended on the two halves sharing a gate. See
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

    // Unsafe-site obligations. This `&[]` is the ONLY production comment list —
    // vcgen has no source-map access and nothing else calls `check_unsafe` — so
    // no SAFETY claim is ever attached (MEASURED, stage2 b1254a567). The mint
    // decides per detected site (`unsafe_verify::detection::decide_site`): a
    // site the separation engine or the compiler already covers mints nothing;
    // `mem::zeroed` / `mem::uninitialized` mint a typed refutation unless the
    // destination type positively admits the pattern; `unreachable_unchecked` is
    // covered by the `VcKind::Unreachable` row arm 1b mints for it; a raw-pointer
    // reborrow (`&*p`) mints a typed `[unsafe:reborrow]` refutation (T10); everything
    // else keeps the byte-frozen `[unsafe] missing SAFETY comment` stand-in.
    // Runs AFTER the separation engine so `unsafe_coverage` holds its rows.
    // `reached_blocks` is the SAME key set arm 1b (`generate::safety`) mints
    // terminator VCs over — `guard_map_for` memoizes `v2_build_path_guard_map`,
    // whose keys are `v2_analyze_path_guards(func).paths` — see
    // `terminator_vc_block_set`.
    if has_intrinsic_unsafe_surface(func) {
        let mut detected_unsafe = unsafe_verify::detect_unsafe_blocks(func);
        if !detected_unsafe.is_empty() {
            unsafe_coverage.reached_blocks = super::guard_map_for(func).keys().copied().collect();
            // THE COMPILER'S OWN ROWS, not a prediction of them. Empty for every
            // caller that is not the compiler, and empty keeps every stand-in.
            unsafe_coverage.compiler_unmodeled_call_blocks =
                crate::compiler_unmodeled_call_blocks_for(&func.def_path);
            // Trust (G1): the compiler's exact zero-validity verdicts for this body's
            // `mem::zeroed::<T>()` calls. Empty for every other caller.
            unsafe_coverage.compiler_zero_valid_zeroed_blocks =
                crate::compiler_zero_valid_zeroed_blocks_for(&func.def_path);
            // Trust (AW-1): rustc's own `.await` `unsafe` calls, as the COMPILER
            // identified them. Empty for every other caller, and empty keeps every row.
            unsafe_coverage.await_desugared_unsafe_call_blocks =
                crate::await_desugared_unsafe_call_blocks_for(&func.def_path);
            unsafe_verify::attach_safety_comments(&mut detected_unsafe, &[]);
            let unsafe_rows = unsafe_verify::generate_safety_vcs(
                func,
                &detected_unsafe,
                box_deref_ops,
                &unsafe_coverage,
            );
            // Inserted at the position taken before the separation rows; the origins record
            // the insertion (`RowSink::splice_at`).
            sink.splice_at(unsafe_rows_at, unsafe_rows);
        }
    }

    // FFI boundary verification with summary-based VCs.
    // Detect Call terminators targeting extern/FFI functions and generate
    // targeted VCs (null checks, range checks, aliasing, return contracts)
    // instead of conservative Bool(true) from unsafe_verify.
    let tp = super::terminator_presence_for(func);
    if tp.has_call || tp.has_tail_call {
        let ffi_db = ffi_summary::FfiSummaryDb::builtin();
        // Trust: 2026-10-25 (FFI-NONNULL-CAST-1) — computed on the first FFI call
        // site only: the fact now asks the local-defs seam about every local, which
        // a body with no FFI call never needs.
        let mut nonnull_locals: Option<std::collections::HashSet<String>> = None;
        let mut buffer_facts = None;
        for block in &func.body.blocks {
            // Trust: round-19 #3 — `is_foreign` (set at extraction from
            // `tcx.is_foreign_item`) is the AUTHORITATIVE FFI signal; the
            // name-substring `is_extern_call` is a fallback for synthetic/test MIR
            // that lacks the flag. A foreign call with no summary lands in
            // `generate_call_site_vcs`' no-summary branch, which fails closed
            // (round-19 #4), so an `extern { fn compute_hash(); }` import can no
            // longer be silently treated as safe.
            let call = match &block.terminator {
                Terminator::Call { func, args, dest, span, is_foreign, callee_key, .. } => {
                    Some((func, args, Some(dest), span, *is_foreign, callee_key.as_ref()))
                }
                Terminator::TailCall { func, args, span, is_foreign, callee_key, .. } => {
                    Some((func, args, None, span, *is_foreign, callee_key.as_ref()))
                }
                _ => None,
            };
            if let Some((callee, args, dest, span, is_foreign, callee_key)) = call
                && (is_foreign || ffi_vcgen::is_extern_call_for(callee, callee_key, ffi_db))
            {
                let mut arg_formulas: Vec<Formula> =
                    args.iter().map(|op| operand_to_formula(func, op)).collect();
                let call_identity =
                    ffi_vcgen::CallIdentity { is_foreign, key: callee_key, arg_count: args.len() };
                let summary = ffi_vcgen::summary_for_call(ffi_db, callee, call_identity);
                // A body with only non-buffer FFI summaries needs no extent analysis.
                let facts = if summary.is_some_and(|summary| !summary.buffer_contracts.is_empty()) {
                    buffer_facts
                        .get_or_insert_with(|| {
                            ffi_buffer_extent::call_facts(func, &tail_call_blocks)
                        })
                        .get(&block.id)
                        .cloned()
                        .unwrap_or_default()
                } else {
                    ffi_buffer_extent::BufferFacts::default()
                };
                // Resolve only the count positions explicitly requested by a summary.
                if let Some(summary) = summary {
                    for contract in &summary.buffer_contracts {
                        if let Some(op) = args.get(contract.count_param)
                            && let Some(count) = facts.count(op)
                            && let Some(arg) = arg_formulas.get_mut(contract.count_param)
                        {
                            *arg = count;
                        }
                    }
                }
                let nonnull_locals = nonnull_locals.get_or_insert_with(|| ffi_nonnull_locals(func));
                // Arg positions whose operand is a whole local with proven
                // non-null provenance (std-container `as_ptr`/`as_mut_ptr` result,
                // reference, or non-deref raw borrow — `ffi_nonnull_locals`).
                // Their `arg == 0` null VCs are UNSAT by construction, so they
                // are discharged at generation instead of being posed over an
                // unconstrained symbol the solver can trivially satisfy.
                let nonnull_args: std::collections::HashSet<usize> = if nonnull_locals.is_empty() {
                    std::collections::HashSet::new()
                } else {
                    args.iter()
                        .enumerate()
                        .filter_map(|(i, op)| match op {
                            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                                nonnull_locals
                                    .contains(place_to_var_name(func, p).as_str())
                                    .then_some(i)
                            }
                            _ => None,
                        })
                        .collect()
                };
                let dest_var = match dest {
                    Some(d) => place_to_var_name(func, d),
                    None => place_to_var_name(func, &Place::local(0)),
                };
                sink.append(ffi_vcgen::generate_call_site_vcs_with_extents(
                    &func.name,
                    callee,
                    &arg_formulas,
                    &dest_var,
                    span,
                    ffi_db,
                    (&nonnull_args, &facts.byte_extents(args)),
                    call_identity,
                ));
            }
        }
    }

    // Atomic ordering legality VCs.
    // Collect atomic operations from Call terminators and check C++ standard
    // legality rules (L1-L5) via MemoryModelChecker::check_operation_legality.
    if tp.has_atomic_call {
        let atomic_ops: Vec<_> = func
            .body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator {
                Terminator::Call { atomic: Some(op), .. }
                | Terminator::TailCall { atomic: Some(op), .. } => Some(op.clone()),
                _ => None,
            })
            .collect();
        if !atomic_ops.is_empty() {
            sink.append(memory_ordering::MemoryModelChecker::check_operation_legality(
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
    // discard frees the partial rows before the discharge/abstract-interp passes.
    if crate::gen_work_tripped() {
        let vc = work_budget_refusal(func);
        return sink.refuse(vc);
    }

    // The per-row passes (SSA version-token normalization, term-`Ite` elimination, the
    // havoc decline and the self-referential-definition refusal) ran on each row as it
    // joined the sink (T3 C08s, `super::row_sink`).
    sink.finish()
}
