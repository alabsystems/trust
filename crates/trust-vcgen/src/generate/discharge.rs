// Generation paired with in-pass discharge, and the substitution machinery it
// needs: sigma actuals (the caller-side values bound to callee parameters),
// call fact tokens, and SSA version normalisation. The tokens must be spelled
// identically here and in the CHC lane or facts minted by one become inert in
// the other.

use trust_types::vc_context::{RowId, VcContext};

use super::*;

/// Generate VCs and run an abstract interpretation pre-pass to discharge
/// VCs provable without a solver.
///
///, #428: Returns `(solver_vcs, preclassified_results)` where
/// `solver_vcs` are VCs that still need a solver and `preclassified_results`
/// are terminal VC results that must not be sent to the solver again. The
/// second bucket can contain interval-analysis proofs and fail-closed
/// `UnsupportedMir` unknowns; callers must inspect each `VerificationResult`
/// instead of treating the whole bucket as proved.
#[must_use]
pub fn generate_vcs_with_discharge(
    func: &VerifiableFunction,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let context = crate::VcgenContext::for_function_inheriting_self_call_identity(&func.def_path);
    crate::with_vcgen_context(&context, || {
        generate_vcs_with_discharge_impl(func, None, false, &FxHashSet::default())
    })
}

/// Summary-aware [`generate_vcs_with_discharge`]: body VCs are generated through
/// the summary-aware safety lane so proved callee postconditions are assumed.
/// `None` is byte-identical to [`generate_vcs_with_discharge`].
pub(super) fn generate_vcs_with_discharge_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
    hardened: bool,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let generation = generate_vcs_with_discharge_and_origins_impl(
        func,
        summaries,
        hardened,
        box_deref_ops,
        KeepOrigins::No,
        None,
    );
    (generation.solver_vcs, generation.discharged)
}

/// The solver-bound rows, the preclassified rows, the id of each in the context the
/// generation wrote into, and the overflow-check origins of both, by index until the entry
/// resolves them to ids (T3 C05, C07, C08s; see `super::overflow_origins`).
pub(super) struct GenerationWithOrigins {
    solver_vcs: Vec<VerificationCondition>,
    /// `solver_rows[i]` is the id of `solver_vcs[i]`: `None` for a row the context refused,
    /// and for every row of a generation that wrote into no context.
    solver_rows: Vec<Option<RowId>>,
    discharged: Vec<(VerificationCondition, VerificationResult)>,
    /// `discharged_rows[i]` is the id of `discharged[i].0`, as `solver_rows`.
    discharged_rows: Vec<Option<RowId>>,
    origins: PendingOrigins,
}

impl GenerationWithOrigins {
    /// The rows of a refused body, split by [`preclassify_unsupported_mir_vcs`], each
    /// interned into `rows` through the row oracle, with no origin table.
    fn preclassified(rows: Option<&mut VcContext>, vcs: Vec<VerificationCondition>) -> Self {
        let (solver_vcs, discharged) = preclassify_unsupported_mir_vcs(vcs);
        Self::without_table(rows, solver_vcs, discharged)
    }

    /// `solver_vcs` and `discharged`, each interned into `rows` through the row oracle,
    /// with no origin table: a refused or degraded body's rows.
    fn without_table(
        mut rows: Option<&mut VcContext>,
        solver_vcs: Vec<VerificationCondition>,
        discharged: Vec<(VerificationCondition, VerificationResult)>,
    ) -> Self {
        let solver_rows = checked_ids(rows.as_deref_mut(), &solver_vcs);
        let discharged_rows = checked_ids(rows, discharged.iter().map(|(vc, _)| vc));
        Self {
            solver_vcs,
            solver_rows,
            discharged,
            discharged_rows,
            origins: PendingOrigins::no_table(),
        }
    }
}

/// [`generate_vcs_with_discharge_impl`], plus the overflow-check origins of the rows
/// it returns when `keep` says so (T3 C05; see `super::overflow_origins`), every row
/// written into `rows` when the caller keeps a context (T3 C08s).
fn generate_vcs_with_discharge_and_origins_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
    hardened: bool,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    keep: KeepOrigins,
    mut rows: Option<&mut VcContext>,
) -> GenerationWithOrigins {
    // OPAQUE-SCALAR-ID-1 / OPAQUE-REF-ID-1: the walk and the discharge below must
    // name each unmodeled carrier identically, so both see the one placed view (see
    // `generate_vcs_impl`).
    let _input_analysis_scope = super::FuncAnalysisScope::enter_if_unbound(func);
    let placed = super::with_placed_opaque_values_cached(func);
    let func = placed.as_ref();
    // INTRINSIC-RESIDUAL-1: the same 128-bit parameter type-range view
    // `generate_vcs_impl` takes (`with_param_type_range_facts`; no clone for a body
    // without a 128-bit parameter).
    let ranged = with_param_type_range_facts(func);
    let func = ranged.as_ref();
    let _analysis_scope = super::FuncAnalysisScope::enter_placed_if_unbound(func);
    if let Some(vc) = crate::memory_image_vc(func) {
        return GenerationWithOrigins::preclassified(rows, vec![vc]);
    }
    // verifier-perf: hold the mid-generation work-meter scope across BOTH the
    // `generate_vcs_impl` obligation walk AND the abstract-interp pre-pass below (both go
    // through owned `place_ty` queries). On the outermost entry this resets the
    // per-function meter; the nested `generate_vcs_impl` call shares one budget. If
    // anything here trips the budget the post-pass check below degrades the whole
    // function to Unknown. SOUNDNESS: DROP-ONLY.
    let _gen_work_scope = crate::gen_work_scope();

    // Trust (BLOCKER 2 — callee effect summaries): install the MIR-derived callee
    // write-sets for this whole entry so the obligation walk AND the
    // abstract-interp pre-pass in `discharge_body_vcs` read the SAME call-havoc
    // oracle. A forked oracle between the version MINT and the fact KILL is the
    // one failure this lane must not introduce; an empty/absent scope is the
    // pre-existing conservative behaviour.
    let _write_sets = callee_write_set::enter_callee_write_sets(summaries);

    let SinkOutput { vcs, ids, origins } = generate_vcs_impl_with_origins(
        func,
        summaries,
        hardened,
        box_deref_ops,
        keep,
        rows.as_deref_mut(),
        super::recipes::Spines::Join,
    );
    let inventory = origins.finish(&vcs);
    discharge_body_vcs_with_origins(func, vcs, ids, inventory, rows)
}

/// The DISCHARGE + augment half of body VC generation: given the RAW
/// pre-discharge obligation set `all_vcs` from [`generate_vcs_impl`], classify
/// unsupported-MIR obligations, run the interval fixpoint, discharge what
/// interval analysis proves, and augment the rest with the abstract state.
///
/// `generate_vcs_with_discharge_impl` is its only caller. (It was split out for
/// the VC-artifact cache, which T4.6 deleted.)
///
/// Deterministic in `(func, all_vcs)` and PURE (no side effects beyond the work
/// meter). Does NOT open its own work scope: the caller owns the scope, so
/// generation and discharge share one budget.
pub(super) fn discharge_body_vcs(
    func: &VerifiableFunction,
    all_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let generation =
        discharge_body_vcs_with_origins(func, all_vcs, Vec::new(), RowInventory::none(), None);
    (generation.solver_vcs, generation.discharged)
}

/// [`discharge_body_vcs`], carrying each row's origin block through the split and the
/// augment, so the overflow-check inventory holds every Add/Sub/Mul overflow row exactly
/// as it leaves: a discharged row as it was, a solver row augmented (T3 C05).
///
/// T3 C08s: `all_ids[i]` is the id of `all_vcs[i]` in `rows` (a missing entry is no id),
/// and each row keeps it through the split: a discharged row, and a solver row the augment
/// left as it was, are the rows that id names; an augmented row joins `rows` through the
/// row oracle as it leaves, and its pre-augment row stays in the context unreferenced.
fn discharge_body_vcs_with_origins(
    func: &VerifiableFunction,
    all_vcs: Vec<VerificationCondition>,
    all_ids: Vec<Option<RowId>>,
    inventory: RowInventory,
    mut rows: Option<&mut VcContext>,
) -> GenerationWithOrigins {
    if let Some(vc) = crate::memory_image_vc(func) {
        return GenerationWithOrigins::preclassified(rows, vec![vc]);
    }
    if all_vcs.is_empty() {
        return GenerationWithOrigins {
            solver_vcs: all_vcs,
            solver_rows: Vec::new(),
            discharged: Vec::new(),
            discharged_rows: Vec::new(),
            origins: inventory.into_origins(Vec::new()),
        };
    }

    let mut solver_candidates = Vec::with_capacity(all_vcs.len());
    // The origin and the id of each solver candidate, parallel to `solver_candidates`.
    let mut candidate_origins: Vec<Option<(BlockId, OriginSite)>> =
        Vec::with_capacity(all_vcs.len());
    let mut candidate_ids: Vec<Option<RowId>> = Vec::with_capacity(all_vcs.len());
    let mut preclassified = Vec::new();
    let mut preclassified_ids: Vec<Option<RowId>> = Vec::new();
    let mut unknown_solver: Option<Symbol> = None;
    for (index, vc) in all_vcs.into_iter().enumerate() {
        let id = all_ids.get(index).copied().flatten();
        if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
            let reason = format!("unsupported MIR `{kind}` preserved in TrustIr: {detail}");
            let solver = *unknown_solver.get_or_insert_with(|| Symbol::intern("trust_vcgen"));
            preclassified.push((
                vc,
                VerificationResult::Unknown {
                    solver,
                    time_ms: 0,
                    reason,
                },
            ));
            preclassified_ids.push(id);
        } else {
            solver_candidates.push(vc);
            candidate_origins.push(inventory.origin(index));
            candidate_ids.push(id);
        }
    }

    if solver_candidates.is_empty() {
        return GenerationWithOrigins {
            solver_vcs: Vec::new(),
            solver_rows: Vec::new(),
            discharged: preclassified,
            discharged_rows: preclassified_ids,
            origins: inventory.into_origins(Vec::new()),
        };
    }

    //, #452: Use type-aware initial state for tighter interval bounds,
    // then compute fixpoint with threshold widening, delayed widening, condition
    // narrowing, and descending narrowing for precision recovery.
    // Abstract interpretation also consumes `func.preconditions` directly;
    // give it the same arithmetic-safe view as VC construction.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let _analysis_scope = super::FuncAnalysisScope::enter_if_unbound(arithmetic_safe_func.as_ref());
    let (unnarrowed_env, merged_env) =
        abstract_interp::merged_interval_environments(arithmetic_safe_func.as_ref());

    // Discharge VCs that interval analysis can prove.
    //
    // Trust (2026-10-10): decided under the environment WITHOUT the def-site narrowing
    // (`narrow_single_assignments_to_their_def`), which the solver rows below are
    // augmented WITH. An interval proof carries no kernel or native proof authority, so
    // the compiler reports a preclassified row runtime-checked, and the bridge's ay
    // producer never sees it. Discharging under the narrowed environment therefore
    // MOVED rows from kernel-certified to runtime-checked (`g[i]` over `let i = match s
    // { Lo => 0, Hi => 5 }` in the falsification corpus), and a native lane given the
    // bare formula refuted a havoc the environment bounds (`*r = 5; *v = w; a[m / 1]`).
    // Sending every newly provable row to the solver instead (review round 118) doubled
    // the solve set of long functions past their budget and exposed rows whose proof
    // reads a versioned name through its base entry, which the conjoined environment
    // does not state. So the narrowing decides which FACTS a row carries, never which
    // lane decides it.
    let merged_env_formula: std::cell::OnceCell<Formula> = std::cell::OnceCell::new();
    let mut solver_vcs = Vec::new();
    let mut solver_rows: Vec<Option<RowId>> = Vec::new();
    let mut discharged = preclassified;
    let mut discharged_rows = preclassified_ids;
    let mut origin_rows: Vec<PendingOriginRow> = Vec::new();
    let keep_origins = !inventory.is_truncated();
    let candidates = solver_candidates.into_iter().zip(candidate_origins).zip(candidate_ids);
    for ((vc, origin), id) in candidates {
        // T3 C07: the inventory names the row by where it left, and the entry names it by
        // its id (`PendingOrigins::resolve`).
        let row = if let abstract_interp::AbstractInterpResult::Discharged(result) =
            abstract_interp::try_discharge_vc(&vc, &unnarrowed_env)
        {
            let at = discharged.len();
            discharged.push((vc, result));
            discharged_rows.push(id);
            EmittedRow::Discharged(at)
        } else {
            // Augment remaining VCs with abstract-state assumptions
            // before solver dispatch. The abstract state is an over-approximation
            // of all concrete executions: adding its constraints as conjuncts to
            // the violation formula narrows the solver's search space without
            // excluding real counterexamples. If the environment is Top (no
            // finite bounds), the VC is returned unchanged.
            let env_formula = merged_env_formula
                .get_or_init(|| abstract_interp::interval_domain_to_formula(&merged_env));
            let at = solver_vcs.len();
            let (augmented, changed) =
                abstract_interp::discharge::augment_owned_vc_with_env_formula(vc, env_formula);
            // T3 C08s: a row the augment left as it was is the row its id names; an
            // augmented row joins the context as it leaves.
            let id = match rows.as_deref_mut() {
                Some(rows) if changed => rows.push_checked_row(&augmented).ok(),
                _ => id,
            };
            solver_vcs.push(augmented);
            solver_rows.push(id);
            EmittedRow::Solver(at)
        };
        // T3 C05: the inventory pairs the origin with the row exactly as it leaves.
        if keep_origins && let Some((block, site)) = origin {
            origin_rows.push(PendingOriginRow { block, site, row });
        }
    }

    // verifier-perf (mid-generation work-bound): if the obligation walk or the
    // abstract-interp pre-pass tripped the per-function work budget, DISCARD everything
    // and degrade the whole function to a single fail-closed Unknown.
    // SOUNDNESS: DROP-ONLY — preclassifies to Unknown, never Proved.
    if crate::gen_work_tripped() {
        let (solver_vcs, discharged) = gen_work_degraded_discharge(func);
        return GenerationWithOrigins::without_table(rows, solver_vcs, discharged);
    }

    GenerationWithOrigins {
        solver_vcs,
        solver_rows,
        discharged,
        discharged_rows,
        origins: inventory.into_origins(origin_rows),
    }
}

/// Build the degraded `(solver_vcs, discharged)` result for a function whose VC-gen
/// tripped the mid-generation work budget: NO solver VCs, and a single `UnsupportedMir`
/// obligation preclassified to Unknown (never Proved). This is the fail-closed wholesale
/// degrade — sound, it can only ADD Unknown.
pub(super) fn gen_work_degraded_discharge(
    func: &VerifiableFunction,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let vc = unsupported_mir_vc(
        func,
        "TrustVcGenWorkBudgetExceeded".to_string(),
        format!(
            "function `{}` exceeded the VC-generation work budget (recursive-datatype \
             clone explosion during generation); its obligations are left Unknown \
             (fail-closed) to keep the rest of the crate verifiable",
            func.name
        ),
        func.span.clone(),
    );
    let reason = if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
        format!("unsupported MIR `{kind}` preserved in TrustIr: {detail}")
    } else {
        "VC-generation work budget exceeded".to_string()
    };
    let result =
        VerificationResult::Unknown { solver: Symbol::intern("trust_vcgen"), time_ms: 0, reason };
    (Vec::new(), vec![(vc, result)])
}

/// Like [`generate_vcs_with_discharge`], but additionally emits caller-side
/// precondition VCs from callee summaries.
///
/// Proved callee postconditions are intentionally not assumed here yet. The VC
/// convention in this crate is "formula is SAT iff a violation exists", so
/// assumptions must be conjoined at a precise, dominated call site after
/// substituting formals/returns into caller locals. A global
/// `postcondition => vc` rewrite is not that model: it has the wrong polarity
/// for this convention and applies facts outside their lifetime. Until the
/// call-site substitution/dominance model exists, the sound default is to
/// leave body VCs unchanged and enforce only callee preconditions.
///
/// Caller-side preconditions are different: a caller must establish a declared
/// callee precondition even when the callee's body has not yet been proved.
/// Those VCs are emitted here so the live compiler path enforces direct-call
/// `#[requires]` contracts instead of only reporting definition-site
/// bookkeeping preconditions.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    generate_vcs_with_discharge_and_summaries_configured(func, summaries, false)
}

/// Compiler integration variant with an explicit, dependency-tracked hardened
/// obligation policy. Library callers default to the deterministic non-hardened
/// set instead of consulting process-global environment state.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries_configured(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let context = crate::VcgenContext::for_function_inheriting_self_call_identity(&func.def_path);
    generate_vcs_with_discharge_and_summaries_configured_with_context(
        func, summaries, hardened, &context,
    )
}

/// Trust (box-deref doc-lint fix): the compiler passes the spans of
/// compiler-synthesized `Box` derefs so the always-`Bool(true)` missing-SAFETY
/// documentation lint is dropped for them (drop-only; see
/// `collect_synthesized_box_deref_ops` in the compiler). Generic over the
/// hasher so the compiler's `rustc_data_structures::fx::FxHashSet` (an alias for
/// the same `rustc_hash::FxHashSet`) passes through unchanged.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries_with_box_deref_ops<S: std::hash::BuildHasher>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    box_deref_ops: &std::collections::HashSet<(BlockId, usize), S>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let context = crate::VcgenContext::for_function_inheriting_self_call_identity(&func.def_path);
    generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
        func,
        summaries,
        false,
        &context,
        box_deref_ops,
    )
}

/// Compiler integration variant with explicit function-owned proof policy.
///
/// The dynamic scope exists only below this API boundary. A synchronously
/// forced callee query can enter with its own context and is guaranteed to
/// restore this frame before caller generation resumes.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries_configured_with_context(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    context: &crate::VcgenContext,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
        func,
        summaries,
        hardened,
        context,
        &FxHashSet::default(),
    )
}

/// The fully-configured entry: explicit hardened obligation policy, explicit
/// function-owned proof-policy context, AND the compiler-synthesized
/// `Box`-deref span set (the union of the `_configured_with_context` and
/// `_with_box_deref_ops` variants above). Generic over the hasher so both
/// this crate's `FxHashSet` and the compiler's
/// `rustc_data_structures::fx::FxHashSet` alias pass through unchanged.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops<
    S: std::hash::BuildHasher,
>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    context: &crate::VcgenContext,
    box_deref_ops: &std::collections::HashSet<(BlockId, usize), S>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let generation = configured_generation(
        func,
        summaries,
        hardened,
        context,
        box_deref_ops,
        KeepOrigins::No,
        None,
    );
    (generation.solver_vcs, generation.discharged)
}

/// The compiler's consumed generation (T3 C07): the rows, each with its id in the body's
/// context, and the overflow-check origins of the rows by id.
///
/// `solver_rows[i]` is the id of `solver_vcs[i]` and `discharged_rows[i]` that of
/// `discharged[i].0`. An id is `None` only for a row the context could not hold (a full
/// table, 2^32 entries), and such a row is still returned and consumed as its eager VC.
/// The eager VCs are authoritative: each id was checked by the row oracle
/// ([`VcContext::check_row`]) when its row was interned, so the row it names reads back
/// as the eager VC in every field.
///
/// Since T3 C08s each row is interned as it joins the generation's row sink, and carries
/// its id through the discharge split; an augmented solver row is interned as it leaves.
/// The context therefore also holds rows no id names: the pre-augment row of each augmented
/// solver row, and the rows that joined a generation the work meter then refused or
/// degraded.
#[derive(Debug)]
pub struct ConsumedGeneration {
    pub solver_vcs: Vec<VerificationCondition>,
    pub solver_rows: Vec<Option<RowId>>,
    pub discharged: Vec<(VerificationCondition, VerificationResult)>,
    pub discharged_rows: Vec<Option<RowId>>,
    pub overflow_origins: OverflowOrigins,
}

/// Intern each of `vcs` into `rows` through the row oracle (T3 C07): the id of each row,
/// in order, `None` where the context refused it.
///
/// UNMETERED (L4-METER-1): this polls no step budget and charges no work meter, so no
/// reproducible stop moves because it ran.
pub fn intern_checked_rows<'a>(
    rows: &mut VcContext,
    vcs: impl IntoIterator<Item = &'a VerificationCondition>,
) -> Vec<Option<RowId>> {
    vcs.into_iter().map(|vc| rows.push_checked_row(vc).ok()).collect()
}

/// Intern each of `vcs` into `rows` through the row oracle, keeping no id (T3 C07p): the
/// `_rows` producers write every row they return into the caller's context this way, and
/// return their eager rows unchanged, which stay what every consumer reads. A row a full
/// context refuses is not interned and is still consumed as itself.
///
/// UNMETERED (L4-METER-1), as [`intern_checked_rows`].
pub fn intern_eager_rows<'a>(
    rows: &mut VcContext,
    vcs: impl IntoIterator<Item = &'a VerificationCondition>,
) {
    for vc in vcs {
        // The id is not kept: the eager row is what the caller returns.
        let _ = rows.push_checked_row(vc);
    }
}

/// The compiler's consumed generation: the fully-configured entry above, plus the
/// overflow-check origins of the rows it returns (T3 C05, design §9.1), every row
/// interned into `rows`, the body's context (T3 C07).
///
/// The origins are the proven-overflow-check elision seam's join table: every
/// Add/Sub/Mul overflow row exactly as this call returns it, named by its id in `rows`,
/// with its origin block, or no table when the generation cannot show its enumeration
/// complete ([`OverflowOrigins::complete`]). They replace `overflow_vc_block_origins`,
/// the replay that regenerated the rows a second time to recover their blocks.
///
/// Each row is interned as it joins the generation's row sink (T3 C08s), inside the
/// generation's work scope; the row oracle that checks each one charges no work meter
/// and polls no budget (L4-METER-1, L4-C08s-3), so it decides nothing the generation
/// decides.
#[must_use]
pub fn generate_vcs_with_discharge_and_overflow_origins<S: std::hash::BuildHasher>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    context: &crate::VcgenContext,
    box_deref_ops: &std::collections::HashSet<(BlockId, usize), S>,
    rows: &mut VcContext,
) -> ConsumedGeneration {
    let GenerationWithOrigins { solver_vcs, solver_rows, discharged, discharged_rows, origins } =
        configured_generation(
            func,
            summaries,
            hardened,
            context,
            box_deref_ops,
            KeepOrigins::Yes,
            Some(rows),
        );
    let overflow_origins = origins.resolve(&solver_rows, &discharged_rows);
    ConsumedGeneration { solver_vcs, solver_rows, discharged, discharged_rows, overflow_origins }
}

/// The body of the two fully-configured entries above, which differ only in whether
/// the overflow-check origins are kept and the rows written into a context.
fn configured_generation<S: std::hash::BuildHasher>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    context: &crate::VcgenContext,
    box_deref_ops: &std::collections::HashSet<(BlockId, usize), S>,
    keep: KeepOrigins,
    rows: Option<&mut VcContext>,
) -> GenerationWithOrigins {
    let owned: FxHashSet<(BlockId, usize)> = box_deref_ops.iter().cloned().collect();
    let out = crate::with_function_vcgen_context(&func.def_path, context, || {
        generate_vcs_with_discharge_and_summaries_configured_impl(
            func, summaries, hardened, &owned, keep, rows,
        )
    });
    // Trust (DIAGNOSTIC ONLY, 2026-09-19): `TRUST_VCGEN_EXIT_TRACE=1` prints each
    // bounds row AS IT LEAVES vcgen. This is the bisection point between
    // `TRUST_SLICE_VC_TRACE` (end of the safety-VC builder, where a failing
    // slice-bounds row's formula is UNSAT and still carries its definitional
    // equations) and `TRUST_AY_SMT_TRACE` (the solver boundary, where those
    // equations are GONE — measured, 5 survive in the passing twin and 0 in the
    // failing row — and the violation is trivially satisfiable).
    //
    // IT IS ON *THIS* ENTRY POINT BECAUSE THE OTHERS ARE OFF-PATH. Placed first
    // in the (since deleted) cross-function cached router, then in its parallel
    // path, then on the bare `generate_vcs`, it printed ZERO rows each time for
    // a program that refutes: the compiler calls THIS function
    // (trust_verify.rs:25393) and dispatches through `trust_router::Router`,
    // not the cached router. Three build cycles
    // spent guessing a module that one read of the call site would have given.
    // A zero from an instrument is a fact about the instrument — placement
    // included. Verdict-neutral.
    static VCGEN_EXIT_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *VCGEN_EXIT_TRACE
        .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_VCGEN_EXIT_TRACE"))
    {
        for vc in &out.solver_vcs {
            if matches!(
                vc.kind,
                trust_types::VcKind::SliceBoundsCheck | trust_types::VcKind::IndexOutOfBounds
            ) {
                let rendered = format!("{:?}", vc.formula);
                // Trust: 2026-09-20 — also print the row's VARIABLE VOCABULARY.
                //
                // Two lanes mint a bounds row and they were measured to use
                // DIFFERENT vocabularies for the same check: the rvalue lane's
                // `collection_len_formula` resolves a slice through
                // `slice_len_formula` to the place-keyed `{place}__slice_len`,
                // while the failing row that reaches the solver names only raw
                // locals and carries no such symbol. eq_count and len cannot
                // tell those apart — two rows can agree on both and still speak
                // about different variables, which is exactly the confusion
                // this class cost three attempts to.
                let vars = rendered_formula_var_names(&rendered);
                // Trust: 2026-09-21 — and the row's LANE, via its obligation
                // record. `index_projection_vc` (the rvalue/projection lane)
                // seeds `ObligationRecord { wrappers: Vec::new(), .. }` and the
                // pipeline then APPENDS one wrapper per fact family it conjoins,
                // so `ob=<n>` distinguishes the two builders that mint the same
                // check: a row with no record at all is neither. Without this
                // the vocabulary column shows THAT two rows disagree and not
                // WHICH builder is responsible, which is the last thing this
                // class needs identified.
                let ob = match &vc.obligation {
                    Some(record) => format!("{}", record.wrappers.len()),
                    None => "none".to_owned(),
                };
                // Trust: 2026-09-21 — and the row's own VIOLATION, truncated.
                // `ob=` says whether a row is recorded and `vars=` says what it
                // can name, but neither says WHICH CHECK the row is about, and
                // a function with two indexing sites emits two rows that agree
                // on kind. Printing the recorded body (or the formula when
                // there is no record) is what distinguishes `w[0]` from
                // `&v[i..]` without guessing from a counterexample.
                let body = match &vc.obligation {
                    Some(record) => format!("{:?}", record.body),
                    None => rendered.clone(),
                };
                // Trust: 2026-09-21 — 140 chars truncated BEFORE the violation
                // clause on a row whose body opens with type ranges, which left
                // "which check does the refuting row state" as an inference.
                // The limit is generous now because the column's whole job is
                // to name the check, and an assembled body front-loads the
                // ranges.
                let body: String = body.chars().take(1200).collect();
                eprintln!(
                    "[vcexit] fn={} kind={:?} ob={} eq_count={} len={} slice_len_syms={} vars=[{}] body={}",
                    func.def_path,
                    vc.kind,
                    ob,
                    rendered.matches("Eq(").count(),
                    rendered.len(),
                    vars.iter().filter(|v| v.ends_with("__slice_len")).count(),
                    vars.join(" "),
                    body,
                );
            }
        }
    }
    ob_criterion_trace(func, &out.solver_vcs);
    out
}

/// Variable names inside a rendered `Formula`, for the `TRUST_VCGEN_EXIT_TRACE`
/// vocabulary column only. Hand-scanned rather than a regex so this diagnostic
/// adds no dependency to the crate. Diagnostic; never read by a verdict.
fn rendered_formula_var_names(rendered: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut rest = rendered;
    while let Some(at) = rest.find("Var(") {
        rest = &rest[at + 4..];
        let Some(open) = rest.find('"') else { break };
        rest = &rest[open + 1..];
        let Some(close) = rest.find('"') else { break };
        names.push(rest[..close].to_owned());
        rest = &rest[close + 1..];
    }
    names.sort_unstable();
    names.dedup();
    names
}

/// Trust (DIAGNOSTIC ONLY, 2026-09-21): is `f` a literal two-sided range on the
/// variable `name` — `And([Le(lit, x), Le(x, lit)])` with `x` that variable?
///
/// This is the shape `mirsem::vc_faithful::range_constraint_parts` recognises (and
/// its parity-checked trust-ir twin in `trust_clean::trustir_safety`), reproduced
/// here rather than shared because those live in a different crate and this is an
/// instrument, not a verdict. The shape is SHALLOW and fully specified, so unlike a
/// recursive walk it carries no exhaustiveness risk.
fn ob_is_type_range_on(f: &trust_types::Formula, name: &str) -> bool {
    use trust_types::Formula as F;
    let F::And(v) = f else { return false };
    let [F::Le(lo, t_lo), F::Le(t_hi, hi)] = v.as_slice() else { return false };
    let is_lit = |x: &F| matches!(x, F::Int(_) | F::UInt(_));
    let names = |x: &F| matches!(x, F::Var(n, _) if n == name);
    is_lit(lo) && is_lit(hi) && t_lo == t_hi && names(&**t_lo)
}

/// Trust (DIAGNOSTIC ONLY, 2026-09-21): every fact a record carries — the conjoined
/// facts of each `ConjoinFactsLast` and the guards of each `PathGuardOr` term. A
/// `PathGuardTerm::Raw` carries no formula.
fn ob_record_facts(rec: &trust_types::ObligationRecord) -> Vec<&trust_types::Formula> {
    use trust_types::{ObligationWrapper as W, PathGuardTerm as P};
    let mut out = Vec::new();
    for w in &rec.wrappers {
        match w {
            W::ConjoinFactsLast { facts } => out.extend(facts.iter()),
            W::PathGuardOr { paths } => {
                for p in paths {
                    if let P::Guarded { guards } = p {
                        out.extend(guards.iter());
                    }
                }
            }
        }
    }
    out
}

/// Trust (DIAGNOSTIC ONLY, 2026-09-21): `TRUST_OB_CRITERION_TRACE=1` prints, per
/// bounds row, whether the discharge criterion of
/// `reports/2026-09-20-the-slice-loop-false-refutation-is-a-second-row.md` FIRES —
/// i.e. whether some free variable of the recorded violation occurs in no fact
/// except a literal two-sided range on that same variable.
///
/// IT MOVES NO VERDICT. The criterion was validated on a 24-row corpus built to
/// exercise ONE class (3/3 on the defects, 1/1 on that corpus's true refutation),
/// and a criterion that turns a refutation into `Unknown` MASKS a real bug when it
/// fires on a true one. So it is measured in the open, across the full gate set,
/// BEFORE anything is wired to it. A row printed `fires=yes` that is a genuine
/// out-of-bounds program is a refutation of the criterion, not a finding about the
/// program.
///
/// Variable names come from the same exhaustive-by-construction Debug scan the
/// `vars=` column uses: it cannot miss a `Var` nested inside a variant a hand-written
/// walk forgot. Its one gap is `SymVar`, which renders without a name — a row using
/// one is printed `symvar=yes` rather than being silently treated as naming less.
fn ob_criterion_trace(func: &VerifiableFunction, vcs: &[VerificationCondition]) {
    static OB_CRITERION_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*OB_CRITERION_TRACE
        .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_OB_CRITERION_TRACE"))
    {
        return;
    }
    for vc in vcs {
        if !matches!(
            vc.kind,
            trust_types::VcKind::SliceBoundsCheck | trust_types::VcKind::IndexOutOfBounds
        ) {
            continue;
        }
        let Some(rec) = &vc.obligation else {
            eprintln!("[obcrit] fn={} kind={:?} ob=none fires=n/a", func.def_path, vc.kind);
            continue;
        };
        let body_rendered = format!("{:?}", rec.body);
        let facts = ob_record_facts(rec);
        let rendered_facts: Vec<String> = facts.iter().map(|f| format!("{f:?}")).collect();
        let symvar = body_rendered.contains("SymVar(")
            || rendered_facts.iter().any(|r| r.contains("SymVar("));
        let mut unpinned: Vec<String> = Vec::new();
        for name in rendered_formula_var_names(&body_rendered) {
            // A variable is PINNED when some fact names it and that fact is not
            // merely its own type range. Ranges are dropped per-variable, not
            // per-fact: one fact can range `x` and constrain `y`.
            let pinned = facts.iter().zip(rendered_facts.iter()).any(|(f, r)| {
                !ob_is_type_range_on(f, &name) && rendered_formula_var_names(r).contains(&name)
            });
            if !pinned {
                unpinned.push(name);
            }
        }
        // Trust: 2026-09-21 — print the FACTS too, truncated. A row whose body
        // has no free variables (a vacuous `Bool(true)` violation) makes
        // `unpinned` trivially empty, so the fires= column alone cannot say
        // whether the row is safe or merely unreadable — and attributing such a
        // row to a lane by matching it against a solver program printed
        // elsewhere is exactly the mistake this file records once already.
        let facts_col: String = rendered_facts
            .iter()
            .map(|r| r.chars().take(90).collect::<String>())
            .collect::<Vec<_>>()
            .join(" ; ");
        eprintln!(
            "[obcrit] fn={} kind={:?} ob={} facts={} symvar={} fires={} unpinned=[{}] factlist=[{}] body={}",
            func.def_path,
            vc.kind,
            rec.wrappers.len(),
            facts.len(),
            if symvar { "yes" } else { "no" },
            if unpinned.is_empty() { "no" } else { "yes" },
            unpinned.join(" "),
            facts_col.chars().take(2000).collect::<String>(),
            body_rendered.chars().take(400).collect::<String>(),
        );
    }
}

pub(super) fn generate_vcs_with_discharge_and_summaries_configured_impl(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    keep: KeepOrigins,
    mut rows: Option<&mut VcContext>,
) -> GenerationWithOrigins {
    // OPAQUE-SCALAR-ID-1 / OPAQUE-REF-ID-1: callsite rows and body rows must share
    // one placed view.
    // PERF-COMPILER-VCGEN-774: hold a `FuncAnalysisScope` across both the callsite
    // precondition pass and the body generation/discharge pass so placement, parameter
    // type-range checks, memory-image detection, body validation, budget checks, and
    // whole-body analyses (`PathGuardAnalysis`, `path_definition_map`, `StmtVersionCtx`,
    // `RowGlobalFacts`, `semantic_guard_map`, `LocalWriteIndex`, `SafetyTerminatorPresence`)
    // are shared across both passes instead of being recomputed.
    let placed = super::with_placed_opaque_values_cached(func);
    let func = placed.as_ref();
    let _placed_scope = super::FuncAnalysisScope::enter_placed_if_unbound(func);
    // INTRINSIC-RESIDUAL-1: the same 128-bit parameter type-range view
    // `generate_vcs_impl` takes (`with_param_type_range_facts`; no clone for a body
    // without a 128-bit parameter).
    let ranged = with_param_type_range_facts(func);
    let func = ranged.as_ref();
    let _ranged_scope = matches!(ranged, std::borrow::Cow::Owned(_))
        .then(|| super::FuncAnalysisScope::enter_placed(func));
    if let Some(vc) = crate::memory_image_vc(func) {
        return GenerationWithOrigins::preclassified(rows, vec![vc]);
    }
    // This entry builds caller-side rows before it reaches `generate_vcs_impl`.
    // Admit the complete public body first so malformed positional MIR cannot
    // mint an otherwise-valid summary obligation alongside the later Unknown.
    if let Err(error) = crate::validate_function(func) {
        let refused = vec![malformed_trust_ir_vc(func, &error)];
        return GenerationWithOrigins::preclassified(rows, refused);
    }

    // verifier-perf: hold the mid-generation work-meter scope across the WHOLE outermost
    // entry — the callsite/guard-map machinery (`generate_callsite_precondition_vcs`) AND
    // the obligation walk (`generate_vcs_with_discharge`) both materialize declared types
    // via owned `place_ty` queries, so they must share ONE per-function budget.
    // Resets on this outermost 0→1 entry; the nested calls share it. SOUNDNESS:
    // DROP-ONLY.
    let _gen_work_scope = crate::gen_work_scope();

    // Trust (BLOCKER 2): the callsite-precondition lane below also consults
    // `terminator_def_names`, so it must see the same refined call-havoc oracle
    // as the body lane (see `generate_vcs_with_discharge_impl`).
    let _write_sets = callee_write_set::enter_callee_write_sets(Some(summaries));

    let callsite_precondition_vcs = generate_callsite_precondition_vcs(func, summaries);

    // Body VCs are generated through the summary-aware lane: each proved callee's
    // postcondition is assumed (conjoined) at the dominated successors of its call,
    // so a downstream obligation that depends on the callee's guarantee can be
    // discharged instead of false-FAILing on a havoced result.
    let mut generation = generate_vcs_with_discharge_and_origins_impl(
        func,
        Some(summaries),
        hardened,
        box_deref_ops,
        keep,
        rows.as_deref_mut(),
    );
    // The callsite rows are appended after the inventory was taken: they are
    // `Precondition` rows, never an Add/Sub/Mul overflow row the seam joins. They join the
    // context as they are appended (T3 C08s).
    if !callsite_precondition_vcs.is_empty() {
        let (callsite_solver_vcs, callsite_preclassified) =
            preclassify_unsupported_mir_vcs(callsite_precondition_vcs);
        generation.solver_rows.extend(checked_ids(rows.as_deref_mut(), &callsite_solver_vcs));
        generation.solver_vcs.extend(callsite_solver_vcs);
        let callsite_discharged = callsite_preclassified.iter().map(|(vc, _)| vc);
        generation.discharged_rows.extend(checked_ids(rows.as_deref_mut(), callsite_discharged));
        generation.discharged.extend(callsite_preclassified);
    }

    // verifier-perf (mid-generation work-bound): if any sub-pass tripped the per-function
    // work budget, DISCARD all accumulated VCs and degrade the whole function to a single
    // fail-closed Unknown. SOUNDNESS: DROP-ONLY — Unknown, never Proved.
    if crate::gen_work_tripped() {
        let (solver_vcs, discharged) = gen_work_degraded_discharge(func);
        return GenerationWithOrigins::without_table(rows, solver_vcs, discharged);
    }
    // T3 C05, belt and braces: an ambient budget trip anywhere in this generation drops
    // the table. The walk's own flag already carries every trip the walk made, and a
    // trip in a later pass cannot unpair a row from its origin (the inventory pairs each
    // row as it leaves), so the table would still be the emitted rows'. The compiler
    // discards such a generation at its checkpoint in any case. This makes the table
    // not depend on that, at no cost to a generation that did not trip.
    if trust_types::verify_budget::exhausted_readonly() {
        generation.origins.mark_truncated();
    }
    generation
}

/// Run body discharge+augment alone on a given raw obligation set, minting
/// the interval proofs in-process, under `context`.
///
/// This is not a compiler verdict path: the compiler always generates and
/// discharges in one call. It is public so tests can drive the discharge half
/// over a hand-built obligation set.
#[must_use]
pub fn discharge_captured_raw_body_with_context(
    func: &VerifiableFunction,
    raw_body: Vec<VerificationCondition>,
    context: &crate::VcgenContext,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    crate::with_function_vcgen_context(&func.def_path, context, || {
        let _gen_work_scope = crate::gen_work_scope();
        discharge_body_vcs(func, raw_body)
    })
}

pub(super) fn preclassify_unsupported_mir_vcs(
    vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let mut solver_vcs = Vec::with_capacity(vcs.len());
    let mut preclassified = Vec::new();
    let mut unknown_solver: Option<Symbol> = None;
    for vc in vcs {
        if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
            let reason = format!("unsupported MIR `{kind}` preserved in TrustIr: {detail}");
            let solver = *unknown_solver.get_or_insert_with(|| Symbol::intern("trust_vcgen"));
            preclassified.push((
                vc,
                VerificationResult::Unknown {
                    solver,
                    time_ms: 0,
                    reason,
                },
            ));
        } else {
            solver_vcs.push(vc);
        }
    }

    (solver_vcs, preclassified)
}

/// Build the σ-substitution formula for a callsite `actual` bound to callee formal `formal`,
/// for the R1 caller-precondition discharge.
///
/// SOUNDNESS (R1 caller-propagation): a const-generic / associated-const / `size_of::<T>()` /
/// otherwise-unevaluated const actual lowers (in `operand_to_formula`) to a by-NAME-interned
/// opaque symbol — before OPAQUE-SCALAR-ID-1 / OPAQUE-REF-ID-1 every `OpaqueScalar` of a
/// given width collapsed to one `__trust_opaque_scalar_uN` and every opaque reference to one
/// `__unknown_const`; today each is named by its site in ITS function, which still collides
/// with the callee's own sites. Two DISTINCT
/// such actuals bound to two DISTINCT callee parameters would then SHARE one symbol, which
/// silently asserts `param_i == param_j` and can turn a satisfiable `¬P[σ]` into a spurious
/// UNSAT — a FALSE discharge (e.g. `helper(M, N)` with inferred `P = a >= b` over const generics
/// `M, N` would certify `¬(S >= S)` UNSAT and "prove" a violable subtraction). The `OpaqueScalar`
/// model invariant requires each occurrence to be an INDEPENDENT fresh symbol; honor it here by
/// re-keying every opaque/unknown actual on its formal, so distinct callee parameters never
/// alias. Strictly weaker than the truth, never falsely proves; concrete actuals (ints, bools,
/// strings — already injective) are untouched, so genuine discharges (e.g. a constant divisor)
/// are unaffected.
pub(super) fn sigma_actual_formula(
    func: &VerifiableFunction,
    formal: &str,
    actual: &Operand,
) -> Formula {
    if let Operand::Constant(c) = actual
        && const_lowers_to_aliasing_opaque(c)
    {
        return Formula::var_owned(format!("__trust_sigma_opaque__{formal}"), Sort::Int);
    }
    // Trust (R1 guarded-caller discharge): the elaborated-drops MIR passes an
    // argument through a FRESH per-call temp — `_6 = copy _2; f(move _6)` — so the
    // actual operand is the un-named temp `_6`, while the caller's dominating guard
    // reads the SAME source value through a DIFFERENT temp — `_4 = copy _2;
    // switchInt(Lt(_4, K))` — which the guard-versioning resolves to the source name
    // (`_2 = x`). Both `_4` and `_6` are `copy _2`, but nothing in the obligation
    // states `_6 == _4`/`_6 == x`, so a guard `x < 4` (over `_4`) cannot discharge
    // `¬(_6 < 4)` and a genuinely-guarded call (`if x < 4 { f(a, x) }`) false-FAILs
    // (an R1 completeness gap, not a soundness bug). Fold the argument temp's
    // whole-local `copy`-chain to its STABLE, source-named root so σ renders `x` —
    // matching the guard's `x` — and the guard discharges. SOUND: the fold only
    // fires when every hop is a unique whole-local `Use(Copy|Move)` and the root is
    // `place_source_is_stable` (single assignment, no slot-write channel — `&mut`,
    // `&raw mut`, `&raw const` of an owned place — no projected or call-dest store,
    // no set-discriminant/deinit), so the temp provably holds the
    // root's unchanged value at the call. A stale-guard vector (`x` reborrowed `&mut`
    // and reassigned before the call) fails `place_source_is_stable` at the root, so
    // σ falls back to the opaque `_6` name and the guard does NOT discharge
    // (fail-closed). Adding the true equality `_6 == x` only REMOVES freedom from the
    // obligation, so it can turn a false-FAIL into a PROVE for a genuine guard but can
    // never mask a real out-of-bounds (a too-weak/off-by-one/other-var guard stays
    // SAT and still fails).
    if let Some(root) = sigma_actual_stable_copy_root(func, actual) {
        return crate::place_to_formula(func, &root);
    }
    operand_to_formula(func, actual)
}

/// R1 guarded-caller discharge: resolve a whole-local argument temp through its
/// `Use(Copy|Move)` copy-chain to the STABLE, source-named root local, so σ names
/// the argument the same way the caller's dominating guard does.
///
/// Returns `Some(root_place)` only when:
///   * `actual` is a whole-local `Copy`/`Move` (no projections — a plain value pass),
///   * every hop of the chain is a UNIQUE whole-local `Use(Copy|Move)` def
///     (`unique_value_def`) — or a UNIQUE whole-local `Rvalue::Cast` whose
///     int→int cast is PROVABLY value-preserving over the FULL source domain
///     (`is_modeled_identity_cast` on `Ty::Int` → `Ty::Int`: same width and
///     signedness, or a widening that is not signed→unsigned) — so the temp is
///     not reseated and provably holds the root's mathematical value, and
///   * the final root local is `place_source_is_stable` (single assignment; no
///     `&mut`/`&raw mut`, projected store, call-dest store, set-discriminant, or
///     deinit) AND carries a source debug name.
///
/// Under those gates the temp provably equals the root's unchanged value, so naming
/// the argument by the root only ADDS the true equality `temp == root`. That can
/// discharge a genuine guard but never mask a real hazard (a too-weak / off-by-one /
/// different-variable guard leaves the obligation SAT). A reseated temp, an unstable
/// root, or a nameless root returns `None`, so σ falls back to the opaque temp name
/// and the caller obligation fails closed.
pub(super) fn sigma_actual_stable_copy_root(
    func: &VerifiableFunction,
    actual: &Operand,
) -> Option<Place> {
    let (Operand::Copy(place) | Operand::Move(place)) = actual else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    // Fuel-bounded: each hop moves to a strictly different local with a unique def,
    // but bound the walk defensively (mirrors `canonicalize_place`'s fuel of 16).
    let mut local = place.local;
    let mut seen = 0u32;
    loop {
        if crate::local_defs::is_parameter(func, local) {
            break;
        }
        seen += 1;
        if seen > 16 {
            return None;
        }
        match crate::local_defs::unique_value_def(func, local) {
            // Follow a whole-local value copy to its source.
            Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src)))
                if src.projections.is_empty() =>
            {
                if src.local == local {
                    return None;
                }
                local = src.local;
            }
            // Follow a whole-local `as` cast to its source — ONLY when the cast is
            // PROVABLY value-preserving for EVERY source value. σ over `Sort::Int`
            // renders both the temp and the root as the same mathematical integer,
            // so following the hop silently asserts `temp == root` over Int; that
            // equality is true unconditionally exactly when the cast is the
            // identity on the value over the FULL source domain:
            //   * unsigned source, wider target (zero-extension), or
            //   * signed source, SIGNED target of >= width (sign-extension into a
            //     signed read-back is the same integer; equal-width signed→signed
            //     is the no-op identity).
            // `is_modeled_identity_cast` is exactly that predicate for
            // `Ty::Int`→`Ty::Int` (same width AND signedness, or a widening that
            // is not signed→unsigned — reused rather than re-derived, so the
            // widths the bridge assigns `usize`/`isize` are honored as declared).
            // Everything else FAILS CLOSED with `None` — narrowing (truncation),
            // signed→unsigned of any width (negative wrap), same-width
            // signedness reinterpret, and any non-`Ty::Int` endpoint (bool /
            // float / pointer — `is_modeled_identity_cast` also admits thin/fn
            // pointer identity casts, but pointer identity is provenance, not an
            // Int-sort value equality, so the explicit `Ty::Int` gate excludes
            // them). `None` here matches today's behavior for a cast def: the
            // chain used to `break` at the temp, whose cast Assign then failed
            // the `local_is_never_written` root gate below.
            Some(Rvalue::Cast(Operand::Copy(src) | Operand::Move(src), to_ty))
                if src.projections.is_empty() =>
            {
                if src.local == local {
                    return None;
                }
                let Some(from_ty) = crate::local_ty_ref(func, src.local) else {
                    return None;
                };
                if !(matches!(from_ty, Ty::Int { .. })
                    && matches!(to_ty, Ty::Int { .. })
                    && crate::is_modeled_identity_cast(from_ty, to_ty))
                {
                    return None;
                }
                local = src.local;
            }
            // A parameter (no whole-local def) or any non-copy def is the chain root.
            _ => break,
        }
    }
    // Require a source-named, UNIQUELY-named root: otherwise `place_to_var_name`
    // falls back to `_{local}`, which does NOT match the guard's source-name read,
    // so the fold would not help (and could, for a shadowed name, mis-key a fact).
    // Checked BEFORE the three whole-body stability scans so unnamed / `_`-prefixed
    // temporaries return `None` in O(1).
    let name = func.body.locals.get(local).and_then(|d| d.name.as_deref())?;
    if name.starts_with('_') {
        return None;
    }
    if crate::has_other_local_with_name(func, local, name) {
        return None;
    }
    // The root must hold a SINGLE FIXED value for the whole body — the entry value of
    // a parameter, unchanged — so the temp provably equals it at the call and the
    // guard's same-named read denotes the same value. Three independent gates, all
    // required:
    //   * `local_is_never_written`: NO assignment statement rewrites the root (a
    //     parameter reassigned even once — `x = x + 1` — has `place_source_is_stable`
    //     `whole_assigns == 1 <= 1` = true, yet its value changed from the entry
    //     value the guard/σ name `x` denotes; this gate rejects it). A never-written
    //     non-parameter local has no value at all and is likewise excluded.
    //   * `place_source_is_stable`: no slot-write channel (`&mut`, `&raw mut`,
    //     `&raw const` of an owned place), projected store, set-discriminant, or
    //     deinit reseats/mutates it (the stale-guard `&mut` vector).
    //   * `local_has_call_dest_write`: NEITHER of the above sees a whole-local
    //     CALL-destination reassign of a PARAMETER (`x = f(..)`):
    //     `local_is_never_written` scans only statements, and
    //     `place_source_is_stable` counts it as the single permitted
    //     `whole_assigns` because a parameter's entry binding is not an explicit
    //     store. Without this gate the fold would equate the temp with a root
    //     whose value CHANGED since entry — one SMT name for two values, a false-
    //     discharge channel. Explicit reject, fail-closed.
    // Together they guarantee the root denotes its fixed entry value at every read.
    //
    // ONE RULE FOR EVERY ROOT, with no parameter arm (VCGEN-NINE-REDS-20261110). The
    // three gates are the def questions themselves, so a parameter root is judged by
    // the same conjunction as any other. PERF-COMPILER-VCGEN-523 had answered a
    // parameter root through `local_versions_collapse_to_bare` instead (identical for
    // a parameter today, and memoized), which is a second, hand-kept copy of this
    // rule that `local_defs_seam_lint` flagged as a parameter arm; de077b9c36
    // (PERF-COMPILER-VCGEN-542..546) then moved the parameter test into a helper the
    // lint cannot see. Keep it one rule here: a parameter arm belongs in the lint's
    // CLASSIFIED list with its reason, or not at all.
    if !(crate::local_is_never_written(func, local)
        && !local_has_call_dest_write(func, local)
        && crate::place_source_is_stable(func, local))
    {
        return None;
    }
    Some(Place::local(local))
}

/// A whole-or-projected CALL-destination write to `local` anywhere in the body.
/// Complements `local_is_never_written` (statement assigns only — call dests are
/// terminators) and `place_source_is_stable` (which admits ONE whole-local
/// call-dest store, the entry construction slot a PARAMETER never uses). Used by
/// stability gates that must mean "the local's value is its entry value at every
/// read".
pub(super) fn local_has_call_dest_write(func: &VerifiableFunction, local: usize) -> bool {
    crate::any_local_write_term(
        func,
        &func.body.blocks,
        local,
        |_block, term| matches!(term, Terminator::Call { dest, .. } if dest.local == local),
    )
}

/// Trust (piece #8 — σ length-rendering): the LENGTH of the ACTUAL slice/array
/// argument `actual` passed at a call site, for the caller `func`, when it can be
/// rendered EXACTLY and STABLY. Returns `Some(len_formula)` only for the three
/// sound sources; anything else returns `None` and the caller emits no length
/// replacement (the callee's `<formal>__slice_len` stays a free var ⇒ `¬P[σ]`
/// SAT ⇒ fail-closed, INV-2).
///
///   * (c) `actual` is a slice whose ROOT the name licence admits (`fill(s, k)` on
///     `s: &mut [T]`; since round A8 also a single-write local such as a call
///     destination `t = make()`): `param_slice_len` follows the copy/reborrow/cast
///     hops to the root and resolves to the caller's own `{root}__slice_len` ONLY
///     when `slice_len_licence` licenses it — the place owning the metadata is
///     `local_defs::path_is_single_static_assignment`, so the name is a name of ONE
///     value, which is the actual's length at the call whatever point the caller's
///     rename versions it at (a twice-written destination is refused, and the
///     member's own spelling then survives for the gate to catch — pinned in
///     `trust-ir-bridge/tests/bundled_member_bounds_charge_real_mir.rs`). The
///     caller's guard `k <= s.len()` discharges `¬(k <= s__slice_len)` through the
///     existing guard machinery.
///   * (a) `actual` is an array→slice UNSIZE cast of a FIXED-size array
///     (`fill(&mut buf, N)` on `buf: [T; 16]`): the reaching def is
///     `Rvalue::Cast(&buf, &mut [T])` whose SOURCE is `&[T; 16]`, so the length is
///     the static constant `16` (`Formula::Int(16)`).
///   * (b) `actual` is an array→slice UNSIZE cast of a CONST-GENERIC array
///     (`fill(buf, M)` on `buf: &mut [T; M]`): the source is `&[T; M]` (SymArray),
///     so the length is the same per-param symbol `M` that the scalar arg `M`
///     renders to — `M <= M` is a tautology.
///
/// SOUNDNESS (INV-2): every source renders the length of the EXACT operand at
/// THIS arg position (the caller zips formals with actuals positionally). Case (a)
/// reads `N` off the immutable array TYPE at the cast; case (b) the immutable
/// SymArray param symbol; case (c) `param_slice_len`, which follows only a
/// parameter-slice reborrow. There is NO path that renders a DIFFERENT slice's
/// length. A non-slice actual, a non-parameter runtime slice, an untraceable cast,
/// or an array whose source type is lost all return `None` (fail-closed).
pub(super) fn sigma_actual_slice_len(
    func: &VerifiableFunction,
    actual: &Operand,
) -> Option<Formula> {
    const TRACE_FUEL: u32 = 16;
    let (Operand::Copy(p) | Operand::Move(p)) = actual else { return None };
    // (c) A parameter-slice reborrow → the caller's own `<param>__slice_len`.
    if let Some(len) = param_slice_len_place(func, p, TRACE_FUEL) {
        return Some(len);
    }
    // (a)/(b) An array→slice unsize cast → the SOURCE array's length. Follow the
    // reaching def of the actual through whole-local `Use` copies to a
    // `Rvalue::Cast(src, &[T]/&mut [T])` whose source is a reference/raw-pointer to
    // a fixed-size `[T; N]` (const `N`) or a const-generic `[T; N]` (SymArray).
    sigma_actual_array_cast_len(func, actual, TRACE_FUEL)
}

/// Trust (piece #8, case a/b): follow the reaching def of `actual` to an
/// array→slice unsize `Rvalue::Cast` and return the SOURCE array's length. The
/// source operand of the cast is a `&[T; N]` / `&mut [T; N]` (a `Ref` of the
/// array), so its type's pointee is the array — `slice_len_formula` on that source
/// operand yields the constant `N` (fixed array) or the SymArray length symbol
/// (const-generic). Fuel-bounded whole-local `Use`-copy walk (no reseating).
pub(super) fn sigma_actual_array_cast_len(
    func: &VerifiableFunction,
    actual: &Operand,
    fuel: u32,
) -> Option<Formula> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = actual else { return None };
    if !p.projections.is_empty() || crate::local_defs::is_parameter(func, p.local) {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local)? {
        // The array→slice unsize (convert.rs lowers `&[T; N] -> &[T]` as this Cast).
        Rvalue::Cast(src, to_ty) if crate::cast_target_is_slice_ref(to_ty) => {
            // `slice_len_formula` on the SOURCE operand reads the array length off
            // its `&[T; N]` / SymArray type — the constant `N` or the const-param
            // symbol. It returns None for a source whose array type was lost
            // (fail-closed). The source is immutable (a reference to the array), so
            // its length cannot change.
            crate::slice_len_formula(func, src)
        }
        // Follow a whole-local value copy of the argument temp to its source.
        Rvalue::Use(inner) => sigma_actual_array_cast_len(func, inner, fuel - 1),
        _ => None,
    }
}

/// Trust (piece #8 — σ length-rendering): append `("<formal>__slice_len", <length
/// of the actual arg>)` replacements for every slice/array formal, so a callee
/// precondition like `n <= arr__slice_len` renders against the caller's ACTUAL
/// length and can discharge. Shared by both the attributed and non-attributed
/// callsite producers so their σ substitutions stay identical.
///
/// A length replacement is emitted ONLY when (i) the summary recorded the formal's
/// type (`param_types`, supplied by R1 and compiler direct-summary paths) AND
/// that type is a slice/array, AND (ii)
/// `sigma_actual_slice_len` can render the actual's length exactly and stably. If
/// either fails, NO replacement is emitted for that formal — the callee's
/// `<formal>__slice_len` stays a free var in `¬P[σ]`, which is SAT, so the caller
/// obligation fails closed (INV-2). Never over-renders: a scalar formal is skipped,
/// and an unrenderable actual leaves the symbol unbound.
pub(super) fn append_length_replacements(
    func: &VerifiableFunction,
    summary: &crate::modular::FunctionSummary,
    args: &[Operand],
    replacements: &mut Vec<(String, Formula)>,
) {
    // `param_types` is parallel to `param_names`; legacy producers leave it empty.
    if summary.param_types.len() != summary.param_names.len() {
        return;
    }
    for ((formal, formal_ty), actual) in
        summary.param_names.iter().zip(summary.param_types.iter()).zip(args.iter())
    {
        if !ty_is_slice_or_array_param(formal_ty) {
            continue;
        }
        if let Some(len) = sigma_actual_slice_len(func, actual) {
            replacements.push((format!("{formal}__slice_len"), len));
        }
    }
}

/// A formal parameter type whose length a callee precondition can reference as
/// `<formal>__slice_len`: a runtime slice (`&[T]`/`&mut [T]`/`*mut [T]`/`[T]`) or
/// a const-generic array (`&[T; N]`/`[T; N]` SymArray). A concrete `[T; N]` /
/// `&[T; N]` is included too (its `<formal>__slice_len` never appears in a callee
/// VC — the callee resolves it to the constant — so a replacement for it is inert
/// but harmless).
pub(super) fn ty_is_slice_or_array_param(ty: &Ty) -> bool {
    match ty {
        Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. } => true,
        Ty::Ref { inner, .. } => {
            matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. })
        }
        Ty::RawPtr { pointee, .. } => {
            matches!(pointee.as_ref(), Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. })
        }
        _ => false,
    }
}

/// Whether ALL version tokens of `local` denote the same value as its BARE
/// name — the license for collapsing `X#tok` → `X`. For a NON-parameter:
/// exactly one whole-local def and no `&mut`/`&raw mut` escape
/// (`is_single_static_assignment`). For a PARAMETER the bar is stricter: the
/// bare name denotes the ENTRY value, and `is_single_static_assignment`
/// counts only explicit defs — a parameter with ONE body reassignment
/// (`x = 4_000_000_000`) passes it while its bare name still means the entry
/// value the stale guard read; collapsing would alias the two and false-PROVE
/// (pinned by `cross_block_bitand_range_guard_dropped_on_reassign`). So a
/// parameter must have NO statement write, NO call-dest write, and pass
/// `place_source_is_stable` (no `&mut` escape / projected store).
///
/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1) — and, for both, no `UnsafeCell` byte of
/// the local's own storage under a shared borrow (`shared_borrowed_cell_places`, which
/// `place_source_is_stable` already asks for a parameter): `poke(&c)` changes an owned
/// `c: Cell<usize>` with no statement write and no `&mut`, so its versions do not all
/// denote its one definition.
pub(super) fn local_versions_collapse_to_bare(func: &VerifiableFunction, local: usize) -> bool {
    // verifier-perf: three whole-body scans per decision, asked once per
    // versioned variable of every formula the collapse pass touches. Pure
    // function of (`func.body`, `local`); memoized per function per scope
    // (`fn_memo`).
    crate::fn_memo::collapse_to_bare(func, local, || {
        let is_param = (1..=func.body.arg_count).contains(&local);
        if is_param {
            crate::local_is_never_written(func, local)
                && !local_has_call_dest_write(func, local)
                && crate::place_source_is_stable(func, local)
        } else {
            is_single_static_assignment(func, local)
                && super::shared_borrowed_cell_places(func, local).is_empty()
        }
    })
}

/// The EXACT variable spelling under which this function's EMITTED VC formulas
/// (post the final `normalize_ssa_version_tokens` pass) read the dest of a
/// `Call dest = callee(..)` terminator in `call_block` — i.e. the token a
/// COMPOSITION lane (e.g. trust-clean's whole-program walk) must rebind an
/// assumed callee-ensures fact onto for the hypothesis to CONNECT to the VC.
///
/// This is the single source of truth pairing the two halves that produce that
/// spelling: `version_terminator_dest_fact` mints the post-call versioned token
/// `{name}#s{call_block}_t`, and `local_versions_collapse_to_bare` licenses the
/// final collapse of every such token to the BARE name when all versions of the
/// dest local provably denote one value (single whole-local def, no `&mut`/raw
/// escape). Duplicating either half out-of-tree re-creates the 2026-07
/// diamond-regression class: a hypothesis minted under a stale spelling is a
/// DISTINCT SMT symbol that silently constrains nothing (fail-open for the
/// composition lane's completeness, never for soundness — the proof just never
/// closes).
///
/// `None` when the dest is projected (a field/index store): no whole-local
/// token exists to rebind onto, so a caller must transfer NOTHING (fail-closed).
#[must_use]
pub fn call_dest_fact_token(
    func: &VerifiableFunction,
    call_block: BlockId,
    dest: &Place,
) -> Option<String> {
    if !dest.projections.is_empty() {
        return None;
    }
    let name = place_to_var_name(func, dest);
    if local_versions_collapse_to_bare(func, dest.local) {
        Some(name)
    } else {
        Some(format!("{name}#s{}_t", call_block.0))
    }
}

/// The LICENSED variable spelling under which this function's EMITTED VC formulas
/// read the value an ARGUMENT operand passes to a `Call` terminator — i.e. the
/// token a COMPOSITION lane (e.g. trust-clean's whole-program walk) may rebind a
/// callee FORMAL onto (in an assumed ensures / an established requires) so the
/// hypothesis speaks about the value the call ACTUALLY receives.
///
/// The pairing partner of [`call_dest_fact_token`], sharing its
/// `local_versions_collapse_to_bare` license: a local's BARE name denotes one
/// value in the emitted VCs only when every version of the local provably
/// denotes that value (single whole-local def; for a PARAMETER additionally no
/// body write and a stable source). A REASSIGNED local's bare name denotes its
/// ENTRY version — the version the function's own preconditions constrain —
/// while the call reads the AT-CALL version, spelled by name-disjoint
/// statement-granular tokens (`a#s{b}_{k}`) with no stable exported single
/// spelling. So:
///
/// - `Some(bare_name)` — the operand is a whole (unprojected) local whose
///   versions collapse to the bare name: the bare spelling IS the at-call value.
/// - `None` — anything else (a constant, a projected place, a reassigned or
///   `&mut`-escaping local): NO licensed spelling exists, and the caller must
///   transfer NOTHING through this formal (fail-closed — dropping a hypothesis
///   only weakens PROVE→OPEN). Minting the bare name anyway is the
///   REASSIGNED-ACTUAL FALSE-HYPOTHESIS bug (2026-07 whole-program probe): the
///   rebound clause binds the ENTRY version the caller's preconditions
///   constrain, not the at-call value, and can falsely certify a genuinely
///   false contract.
#[must_use]
pub fn call_arg_fact_token(func: &VerifiableFunction, arg: &Operand) -> Option<String> {
    match arg {
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && local_versions_collapse_to_bare(func, p.local) =>
        {
            Some(place_to_var_name(func, p))
        }
        _ => None,
    }
}

/// A BARE-named copy of a version-tokened guard, valid when every renamed base
/// is single-static-assignment. `version_terminator_dest_fact` names a call
/// dest's fact with its terminal token (`_5#s0_t == ite(..)`), but a callsite
/// ¬P[σ] renders the SAME local by its BARE σ-actual name (`_5`) — two SMT
/// names for one value, so the fact never constrains the obligation and a
/// spurious counterexample survives (`_5 = 1, _5#s0_t = 0`). For an SSA local
/// the versioning is vacuous — one write means every version token and the
/// bare name denote the SINGLE assigned value — so renaming `base#tok → base`
/// for SSA bases is an identity on the fact's meaning. Non-SSA versioned vars
/// are left untouched (identity on the rest keeps the fact true); returns
/// `None` when no rename fires.
#[inline]
fn collect_ssa_collapse_renames(
    func: &VerifiableFunction,
    formula: &Formula,
) -> (Vec<(String, Formula)>, bool) {
    let mut renames: Vec<(String, Formula)> = Vec::new();
    let mut seen: FxHashSet<&str> = FxHashSet::default();
    let mut needs_full_subst = false;
    trust_types::visit_formula_nodes(formula, &mut |f| match f {
        Formula::Forall(..) | Formula::Exists(..) => {
            needs_full_subst = true;
        }
        Formula::Var(name, sort) => {
            let Some((base, tok)) = name.split_once('#') else {
                return;
            };
            if !needs_full_subst
                && tok.bytes().any(crate::is_projection_segment_lead)
                && !base.bytes().any(crate::is_projection_segment_lead)
            {
                needs_full_subst = true;
            }
            // A loop-transition HAVOC is not a second spelling of the bare
            // local; collapsing it would assert the iteration left the local
            // unchanged. See `LOOP_TRANSITION_HAVOC_TOKEN_PREFIX` for the
            // measured false proof this excludes.
            if !crate::version_token_is_loop_transition_havoc(name)
                // Nor is a TINV unwind havoc (`TINV_UNWIND_HAVOC_TOKEN_PREFIX`).
                && !crate::version_token_is_tinv_unwind_havoc(name)
                // Nor a guard-local path-guard spelling (`GUARD_VALUE_TOKEN_PREFIX`).
                && !crate::version_token_is_guard_value(name)
                && seen.insert(name.as_str())
            {
                // verifier-perf: the "which local mints this base" search is a table
                // lookup built once per function per scope (`fn_memo`) — the
                // linear `find` over every local, each step a full name mint, was
                // being re-run for every versioned variable of every formula.
                let base_local = crate::fn_memo::whole_local_index_by_base(func, base, |l| {
                    crate::place_to_var_name(func, &Place::local(l))
                });
                if let Some(local) = base_local
                    && local_versions_collapse_to_bare(func, local)
                {
                    renames.push((
                        name.clone(),
                        Formula::var_owned(base.to_string(), sort.clone()),
                    ));
                }
            }
        }
        _ => {}
    });
    (renames, needs_full_subst)
}

fn rewrite_exact_hash_vars_small(formula: Formula, renames: &[(String, Formula)]) -> Formula {
    match formula {
        Formula::Var(name, sort) => {
            if name.as_bytes().contains(&b'#')
                && let Some((_, repl)) = renames.iter().find(|(formal, _)| *formal == name)
            {
                return repl.clone();
            }
            Formula::Var(name, sort)
        }
        other => other.map_children(&mut |child| rewrite_exact_hash_vars_small(child, renames)),
    }
}

fn rewrite_exact_hash_vars_indexed(
    formula: Formula,
    renames: &FxHashMap<&str, &Formula>,
) -> Formula {
    match formula {
        Formula::Var(name, sort) => {
            if name.as_bytes().contains(&b'#')
                && let Some(repl) = renames.get(name.as_str())
            {
                return (*repl).clone();
            }
            Formula::Var(name, sort)
        }
        other => other.map_children(&mut |child| rewrite_exact_hash_vars_indexed(child, renames)),
    }
}

fn apply_ssa_collapse_renames_owned(
    formula: Formula,
    renames: &[(String, Formula)],
    needs_full_subst: bool,
) -> Formula {
    if needs_full_subst {
        return substitute_summary_params_owned(formula, renames);
    }
    if renames.len() <= 8 {
        rewrite_exact_hash_vars_small(formula, renames)
    } else {
        let mut indexed: FxHashMap<&str, &Formula> =
            FxHashMap::with_capacity_and_hasher(renames.len(), Default::default());
        for (k, v) in renames {
            indexed.insert(k.as_str(), v);
        }
        rewrite_exact_hash_vars_indexed(formula, &indexed)
    }
}

pub(super) fn bare_ssa_guard_variant(
    func: &VerifiableFunction,
    guard: &Formula,
) -> Option<Formula> {
    let (renames, needs_full_subst) = collect_ssa_collapse_renames(func, guard);
    if renames.is_empty() {
        return None;
    }
    Some(apply_ssa_collapse_renames_owned(guard.clone(), &renames, needs_full_subst))
}

/// Collapse every versioned occurrence `X#tok` of a SINGLE-STATIC-ASSIGNMENT
/// local `X` to the bare name, across a whole VC formula. For an SSA local the
/// version tokens are vacuous — one write means the establish token, every
/// terminal token, and the bare name all denote the single assigned value —
/// so the collapse is an identity on the formula's meaning that CONNECTS
/// facts the token spellings kept apart (`h <= 16` bare from the global
/// min/max facts vs an establish-versioned body read `h#s6_t`, which
/// otherwise lets a refutation assign them different values). Reassigned
/// locals keep their tokens untouched: their disjointness is load-bearing
/// (the staleness kill works by name-disjointness). Field-projected bases
/// (`_14.0#s5_0`) do not resolve to a whole local and are left alone.
pub(super) fn normalize_ssa_version_tokens(
    func: &VerifiableFunction,
    formula: &Formula,
) -> Formula {
    let (renames, needs_full_subst) = collect_ssa_collapse_renames(func, formula);
    if renames.is_empty() {
        return formula.clone();
    }
    apply_ssa_collapse_renames_owned(formula.clone(), &renames, needs_full_subst)
}

/// Owned counterpart of [`normalize_ssa_version_tokens`] that returns `formula` untouched
/// when no SSA version tokens need collapsing and transforms in place otherwise.
pub(super) fn normalize_ssa_version_tokens_owned(
    func: &VerifiableFunction,
    formula: Formula,
) -> Formula {
    let (renames, needs_full_subst) = collect_ssa_collapse_renames(func, &formula);
    if renames.is_empty() {
        return formula;
    }
    apply_ssa_collapse_renames_owned(formula, &renames, needs_full_subst)
}

/// True for the `ConstValue` variants that `operand_to_formula` lowers to a by-name-interned
/// opaque symbol (so two distinct occurrences alias). The concrete/injective variants — Bool,
/// Int, Uint, Float, FloatBits, Unit, CallableItem, Str — are excluded (each lowers to a literal
/// value or an injectively-named term). Everything else (`OpaqueScalar` and any unevaluated/unknown variant
/// that hits `operand_to_formula`'s `__unknown_const` fallback) is opaque and MUST be freshened
/// per occurrence. Kept as a deny-list of the known-injective variants so a future `ConstValue`
/// addition defaults to the SOUND (freshened) side.
pub(super) fn const_lowers_to_aliasing_opaque(c: &ConstValue) -> bool {
    !matches!(
        c,
        ConstValue::Bool(_)
            | ConstValue::Int(_)
            | ConstValue::Uint(..)
            | ConstValue::Float(_)
            | ConstValue::FloatBits { .. }
            | ConstValue::Unit
            | ConstValue::CallableItem { .. }
            | ConstValue::Str { .. }
            // Trust (piece #8, case b): a const-generic PARAM value (`M`) is NOT an
            // aliasing opaque — it lowers to the ONE canonical, stable per-param
            // symbol `__trust_constparam_{index}_{name}` (`operand_to_formula`'s
            // `ConstParam` arm), the SAME term a const-generic array length renders
            // to. σ must render it AS that symbol (not a fresh `__trust_sigma_opaque__n`)
            // so a precondition `n <= arr__slice_len` at `fill(buf, M)` on
            // `buf: &[u32; M]` becomes `M <= M` (a tautology) and discharges. Sound:
            // the symbol is unconstrained (asserts no value) and per-param-identity
            // keyed, so two distinct params `M`, `N` stay distinct.
            | ConstValue::ConstParam { .. }
    )
}

/// True for the opaque symbol families `operand_to_formula` produces for alias-prone
/// carriers: `__trust_opaque_scalar_*` (OpaqueScalar), `__trust_opaque_ref_*` (the
/// opaque-reference carriers), `__trust_unsupported_operand_*`, and the `__unknown_*`
/// fallbacks. Within one function the scalar/reference/unsupported names are per
/// occurrence (OPAQUE-SCALAR-ID-1, OPAQUE-REF-ID-1); a callsite formula mixes two
/// functions' sites, so the families are still freshened there. NOT the σ namespace
/// `__trust_sigma_opaque__*`, which is already per-formal-distinct (`sigma_actual_formula`)
/// and must be left intact so `¬P[σ]` remains structurally equal to `¬substituted` for the
/// discharge gate. NOT the const-generic family `__trust_constparam_*` either: it is keyed
/// on the param's identity, so within one σ obligation one symbol is one value of the
/// caller (see the soundness argument in the body; CONSTPARAM-SIGMA-FRESHEN-1).
pub(super) fn is_aliasing_opaque_symbol_name(name: &str) -> bool {
    // The COMPLETE set of by-name-interned opaque/unknown symbols (enumerated against
    // operand_to_formula, lib.rs ~2150-2214) — each keyed only by width/type/kind, never by
    // value, so two distinct values collapse onto one symbol:
    //   __trust_opaque_scalar_{u,i}{width}_*  OpaqueScalar (assoc-const / size_of / runtime
    //                                       value). Since OPAQUE-SCALAR-ID-1 the suffix is
    //                                       the occurrence's site or constant key, so the name
    //                                       is per-value WITHIN one function; a callsite σ
    //                                       formula mixes two functions' sites, so the whole
    //                                       family is still freshened per occurrence here.
    //   __trust_opaque_ref_*                OpaqueConst / UnitVariantRef / StructScalarFieldsRef.
    //                                       Since OPAQUE-REF-ID-1 the suffix is the occurrence's
    //                                       site (it was the ONE symbol `__unknown_const`);
    //                                       per-value within one function, freshened here for
    //                                       the same cross-function reason as the scalar family.
    //   __unknown_const                     fallback for a ConstValue variant with no identity arm
    //   __trust_unsupported_operand_*       refused operand, named by its site since
    //                                       OPAQUE-REF-ID-1 (was keyed by kind/detail text)
    //   __unknown_operand                   unknown-Operand fallback
    // EXCLUDED (injective, must NOT be freshened): __trust_float_bits_* (by bits), Str (by bytes),
    // __trust_callable_reify_{dest} (by dest), plain places `_n`, the σ namespaces
    // __trust_sigma_opaque__* / __trust_sigma_constparam__* (already per-formal / per-callee-
    // param distinct; freshening them would break `¬P[σ] == ¬substituted` at the discharge gate),
    // and — since CONSTPARAM-SIGMA-FRESHEN-1 (2026-10-11) — the const-generic family
    //   __trust_constparam_{index}_{name}   const-generic PARAM value / array length (piece #7a)
    //
    // Trust (CONSTPARAM-SIGMA-FRESHEN-1): the const-generic family is IDENTITY-keyed, not
    // width-keyed, so it is not alias-prone and is NOT in this set. It used to be, on the
    // argument that `helper(M, N)` would alias `M` and `N` on the σ path — true of the
    // pre-piece-#7a `(width, signed)` key, false since: `M` and `N` mint `__trust_constparam_0_M`
    // and `__trust_constparam_1_N`, and `helper(M, M)` shares one symbol because the two
    // actuals ARE one value. Freshening the family split the caller's ONE `K` into
    // `__trust_constparam_0_K__r1occ{n}`, one per occurrence, which detached the guard `n < K`
    // from the unsize fact `_4__slice_len == K` and from σ's `buf__slice_len := K`: the correct
    // `if n < K { pick(a, n) }` on `a: &[u32; K]` was refuted (`[precond] FAILED`, default
    // rc 1), and the R1 flip of a private `idx(a, i)` behind such a guard was refused —
    // measured on the stage 1 of `5911b1325f` (`tests/ui/trust/const_param_sigma_caller_guard.rs`
    // `ok`, `r1`) and of `2bf0ad72e3` (the wave-22 scout's probes). By the same split, the
    // `fill(buf, M)` tautology the piece #8 comment on `const_lowers_to_aliasing_opaque`
    // promises read `M_occ0 <= M_occ1`, which cannot discharge (read from the code, not run).
    //
    // WHY SHARING IS SOUND — no σ obligation can hold two DISTINCT const-param values under
    // one `__trust_constparam_*` symbol. Every conjunct of the three σ assemblies
    // (`generate_callsite_precondition_vcs{,_attributed}`, `generate_callsite_l0_replay_candidates`)
    // comes from one of:
    //   (a) the CALLER's own body: block defs, path defs, path guards, semantic guards, global
    //       facts and the caller's own stable `requires`. Every family leaf there is minted from
    //       a `ConstValue::ConstParam` / `Ty::SymArray` of the caller's MIR
    //       (`operand_to_formula`, `slice_len_formula`, `value_facts`, `chc`), i.e. from a rustc
    //       `ParamConst { index, name }` of the caller's body, whose `index` is the param's
    //       position in the caller's generics (parents included) and so unique per param;
    //       `trust_types::const_param_symbol` is injective on `(index, name)`. One symbol is
    //       one param of the caller, and a const param is ONE value for a whole execution of
    //       the body. (MIR inlining instantiates an inlined body's params with the call's
    //       arguments, so inlined code too names only the caller's params.)
    //   (b) callee SUMMARY facts injected as semantic guards: `rebind_callee_postconditions`
    //       admits only clauses whose free variables are formals and `_0`
    //       (`postcondition_rebindable`, `precondition_rebindable` for the antecedent), all
    //       replaced by caller-side formulas, so a callee's own family leaf drops the clause;
    //       return-value summaries are integer literals.
    //   (c) σ's replacement VALUES: `sigma_actual_formula` / `sigma_actual_slice_len` over the
    //       caller's operands — (a) again — or the `__trust_sigma_*` fresh names.
    //   (d) the CALLEE's `P` itself — the one foreign formula. In the two precondition
    //       producers, `isolate_callee_const_param_symbols` renames every FREE family leaf of
    //       `P` into `__trust_sigma_constparam__*` BEFORE σ, so a callee's `M` can never be
    //       read as a caller's `M` (pinned by
    //       `const_param_fold_tests::callee_const_param_cannot_meet_the_callers_symbol`).
    //       In the replay lane the callee violation's non-formal leaves are temps that must
    //       be def-pinned and are renamed into `__trust_replay__*`, or the candidate drops.
    // No producer today puts a family leaf into `P` (a source contract cannot name a const
    // param and spells a length `<formal>__slice_len`; R1 and the derived-requires lane take
    // `P` from a monomorphic body), so (d) is defence in depth.
    //
    // The replay lane (refutation-only) no longer meets a caller's const param as a
    // `__r1occ` name, which it rejected by name; it now meets the shared symbol, which
    // `composed_formula_is_caller_entry_grounded` classifies like any non-parameter name:
    // admitted only when a conjunct def-pins it to entry state, else the candidate drops.
    name.starts_with(trust_types::OPAQUE_SCALAR_SYMBOL_PREFIX)
        || name.starts_with(trust_types::OPAQUE_REF_SYMBOL_PREFIX)
        || name == "__unknown_const"
        || name.starts_with(trust_types::UNSUPPORTED_OPERAND_SYMBOL_PREFIX)
        || name == "__unknown_operand"
}

/// Per-OCCURRENCE freshen every alias-prone opaque symbol leaf in `formula`.
///
/// SOUNDNESS (R1 caller-propagation, complete alias fix): associated-const / `size_of` /
/// unevaluated-const operands lowered (in `operand_to_formula`) to a single by-name-interned
/// symbol per `(width,signed)` — today per site within ONE function (OPAQUE-SCALAR-ID-1), which
/// still collides across the two functions a σ obligation mixes — so two DISTINCT such values
/// could collapse to ONE symbol and silently assert an equality between unrelated terms. (A
/// const-generic PARAM is not in the family: its symbol is identity-keyed, one value per
/// symbol; see `is_aliasing_opaque_symbol_name`.) The σ-substitution surface is fixed locally
/// (`sigma_actual_formula`), but the SAME interned symbol re-enters the discharge obligation as a
/// SUB-operand through many guard/semantic-fact helpers (bool-temp resolution, the BinaryOp/Cast
/// semantic arms, checked-arith results, min/max/clamp facts). Rather than chase every syntactic
/// site, this single structural post-pass over the FINAL obligation gives every such leaf an
/// INDEPENDENT fresh name (`{name}__r1occ{n}`), honoring the `OpaqueScalar` model invariant
/// ("each occurrence an independent fresh symbol"). Splitting a shared symbol only REMOVES
/// implied equalities ⇒ the obligation can only move SAT-ward ⇒ `certify_vc`'s UNSAT (discharge)
/// set strictly shrinks ⇒ a previously-false discharge is killed, a genuine one is preserved.
/// The fresh leaf KEEPS THE LEAF'S OWN SORT: not every alias-prone opaque is `Sort::Int` (a
/// `bool` const-generic, `ConstParam { width: 1, signed: false }`, minting `Sort::Bool`, was in
/// this family until CONSTPARAM-SIGMA-FRESHEN-1, and the previous hardcoded `Sort::Int` handed
/// the solver an ill-typed `And`/`Not` operand on the σ path). Sort is orthogonal to the
/// argument above: renaming splits equalities whatever the sort is.
fn formula_has_aliasing_opaque_occurrence(formula: &Formula) -> bool {
    trust_types::any_formula_node(formula, &mut |node| {
        node.var_name().is_some_and(is_aliasing_opaque_symbol_name)
    })
}

pub(super) fn freshen_aliasing_opaque_occurrences(
    formula: &Formula,
    counter: &std::cell::Cell<u32>,
) -> Formula {
    if !formula_has_aliasing_opaque_occurrence(formula) {
        return formula.clone();
    }
    freshen_aliasing_opaque_occurrences_rec(formula.clone(), counter)
}

/// Owned counterpart of [`freshen_aliasing_opaque_occurrences`] that returns `formula`
/// untouched when no alias-prone opaque leaf is present and transforms in place otherwise.
pub(super) fn freshen_aliasing_opaque_occurrences_owned(
    formula: Formula,
    counter: &std::cell::Cell<u32>,
) -> Formula {
    if !formula_has_aliasing_opaque_occurrence(&formula) {
        return formula;
    }
    freshen_aliasing_opaque_occurrences_rec(formula, counter)
}

fn freshen_aliasing_opaque_occurrences_rec(
    formula: Formula,
    counter: &std::cell::Cell<u32>,
) -> Formula {
    if let Some(name) = formula.var_name()
        && is_aliasing_opaque_symbol_name(name)
    {
        let n = counter.get();
        counter.set(n + 1);
        let sort = formula.var_sort().cloned().unwrap_or(Sort::Int);
        return Formula::var_owned(format!("{name}__r1occ{n}"), sort);
    }
    formula.map_children(&mut |child| freshen_aliasing_opaque_occurrences_rec(child, counter))
}

/// The σ namespace a CALLEE's own const-generic parameter symbols are moved into before σ
/// substitution (CONSTPARAM-SIGMA-FRESHEN-1; see [`isolate_callee_const_param_symbols`]). It
/// starts with `__trust_sigma_`, the prefix the replay lane rejects as a deliberately free σ
/// var, and contains `__`, so no source place can spell it (`place_to_var_name` demotes such a
/// name, `trust_types::source_contract_synthetic_name_collision` rejects it in a contract).
pub(super) const SIGMA_CALLEE_CONST_PARAM_PREFIX: &str = "__trust_sigma_constparam__";

/// Trust (CONSTPARAM-SIGMA-FRESHEN-1, defence in depth): rename every FREE
/// `__trust_constparam_*` leaf of a CALLEE's precondition `P` into
/// [`SIGMA_CALLEE_CONST_PARAM_PREFIX`], BEFORE σ substitution.
///
/// WHY. `trust_types::const_param_symbol` is keyed on a param's identity WITHIN ONE ITEM, so a
/// callee's `M` and a caller's `M` at the same index spell the same symbol. A family leaf in
/// `P` names the callee INSTANCE's param, whose value at this call is the call's generic
/// argument, not the caller's same-spelled param. σ obligations no longer freshen the family
/// (it is one value per symbol on the caller's side), so such a leaf left as is would be read
/// as the caller's `M`: `P = n < __trust_constparam_0_M` at `g::<2>(b, n)` inside a caller
/// guarding `n < M` would discharge — a false PROVE. No producer puts a family leaf into `P`
/// today (a source contract cannot name a const param and spells a length
/// `<formal>__slice_len`; R1 and the derived-requires lane read a monomorphic body), so this
/// closes the channel structurally rather than by that census.
///
/// SOUND. All occurrences of one callee param land on ONE σ name (they are one value of the
/// callee instance), disjoint from every caller-side name: σ's replacement values mint only
/// `__trust_sigma_opaque__*` / `__trust_sigma_field__*`, and no source place can spell the
/// prefix. The renamed symbol is FREE in the obligation, so it asserts nothing: `¬P[σ]` can
/// only move SAT-ward and the call site fails closed. On a `P` without a free family leaf
/// (every producer today) this is the identity.
///
/// BINDER-AWARE. Only FREE occurrences are renamed: renaming a bound occurrence changes the
/// formula's meaning in either direction (`∃x. x != x` is false, `∃x. y != x` is valid). A
/// quantifier in `P` binding a name in the σ const-param namespace could capture a renamed
/// leaf; such a `P` becomes `Bool(false)`, the impossible caller obligation (fail-closed;
/// nothing mints such a binder).
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn isolate_callee_const_param_symbols(precondition: &Formula) -> Formula {
    isolate_callee_const_param_symbols_cow(precondition).into_owned()
}

pub(super) fn isolate_callee_const_param_symbols_cow(
    precondition: &Formula,
) -> std::borrow::Cow<'_, Formula> {
    fn rename_free(formula: Formula, bound: &FxHashSet<String>) -> Formula {
        if let Some(name) = formula.var_name()
            && let Some(rest) = name.strip_prefix(trust_types::CONST_PARAM_SYMBOL_PREFIX)
            && !bound.contains(name)
        {
            let sort = formula.var_sort().cloned().unwrap_or(Sort::Int);
            return Formula::var_owned(format!("{SIGMA_CALLEE_CONST_PARAM_PREFIX}{rest}"), sort);
        }
        match formula {
            Formula::Forall(bindings, body) => {
                let body = if bindings.is_empty() {
                    Box::new(rename_free(*body, bound))
                } else {
                    let mut inner = bound.clone();
                    inner.extend(bindings.iter().map(|(sym, _)| sym.as_str().to_string()));
                    Box::new(rename_free(*body, &inner))
                };
                Formula::Forall(bindings, body)
            }
            Formula::Exists(bindings, body) => {
                let body = if bindings.is_empty() {
                    Box::new(rename_free(*body, bound))
                } else {
                    let mut inner = bound.clone();
                    inner.extend(bindings.iter().map(|(sym, _)| sym.as_str().to_string()));
                    Box::new(rename_free(*body, &inner))
                };
                Formula::Exists(bindings, body)
            }
            other => other.map_children(&mut |child| rename_free(child, bound)),
        }
    }
    if !trust_types::any_formula_node(precondition, &mut |node| {
        node.var_name()
            .is_some_and(|name| name.starts_with(trust_types::CONST_PARAM_SYMBOL_PREFIX))
    }) || !trust_types::any_free_variable_name(precondition, &mut |name| {
        name.starts_with(trust_types::CONST_PARAM_SYMBOL_PREFIX)
    }) {
        return std::borrow::Cow::Borrowed(precondition);
    }
    if trust_types::any_formula_node(precondition, &mut |node| {
        matches!(
            node,
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _)
                if bindings
                    .iter()
                    .any(|(sym, _)| sym.as_str().starts_with(SIGMA_CALLEE_CONST_PARAM_PREFIX))
        )
    }) {
        return std::borrow::Cow::Owned(Formula::Bool(false));
    }
    std::borrow::Cow::Owned(rename_free(precondition.clone(), &FxHashSet::default()))
}

/// The subset of the CALLER's own `#[requires]` preconditions that may be conjoined
/// BARE-NAMED onto any of its callsite-precondition obligations.
///
/// SOUNDNESS: a def-site `requires` is a fact about the ENTRY values of the caller's
/// formals (the caller's own body VCs already assume it under exactly that reading —
/// see `conjoin_preconditions_versioned`'s `Fact::entry`). When every free variable
/// of the formula denotes a formal that is NEVER reassigned — no whole-or-projected
/// store, no call-dest write, no `&mut`/`&raw mut` escape — its bare source name
/// denotes that unchanged entry value at EVERY program point of the body, so
/// conjoining the formula onto a callsite obligation anywhere in the body is sound.
/// A formal that IS reassigned (or escapes) fails the gate and its precondition is
/// DROPPED — fail-closed: the obligation stays exactly as strong as today (dropping
/// a hypothesis can only turn a discharge into a refutation, never the reverse).
///
/// Deliberately NOT `conjoin_preconditions_versioned`: that lane version-renames the
/// VC body unconditionally (`version_rename_at`), which would rewrite `¬P[σ]` and
/// break the attributed twin's structural `not_p` matching (the `guards` extraction
/// and trust-router's `is_admissible_caller_discharge` both require `¬P[σ]` to
/// survive VERBATIM as a direct conjunct). Here the preconditions are spliced flat
/// as ordinary guard conjuncts instead, under the strictly stronger never-reassigned
/// gate that makes the rename unnecessary.
pub(super) fn stable_caller_preconditions(func: &VerifiableFunction) -> Vec<Formula> {
    func.preconditions
        .iter()
        .filter(|pre| {
            if contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre) {
                return false;
            }
            // Binder-aware free variables (quantifier-bound names excluded), same
            // walk `postcondition_rebindable` uses. A closed formula (no free
            // vars) is a constant fact of the contract and passes vacuously.
            trust_types::all_free_variable_names(pre, &mut |name| {
                caller_precondition_var_is_entry_stable(func, name)
            })
        })
        .cloned()
        .collect()
}

/// True iff `name` (a free variable of a caller `#[requires]`) provably denotes the
/// unchanged ENTRY value of a caller formal at every program point of the body.
/// Every gate is required; any miss FAILS CLOSED (the precondition is dropped):
///   * the name is not `_`-prefixed and names EXACTLY ONE local — otherwise it
///     could collide with `place_to_var_name`'s `_{index}` fallback or a shadowed
///     binding (mirrors `sigma_actual_stable_copy_root`'s root-naming gate);
///   * the local is a PARAMETER (`1..=arg_count`) — only a parameter has a defined
///     entry value for the `requires` to constrain;
///   * the parameter's declared type is a by-value scalar (`Ty::Int`/`Ty::Bool`) —
///     a reference/ADT formal can have its INTERIOR mutated through a shared
///     re-borrow (interior mutability) without tripping any reassignment gate
///     below, which would let a stale entry fact discharge a live obligation;
///   * gate pair on reassignment — BOTH required, exactly as in
///     `sigma_actual_stable_copy_root` (neither alone suffices, and neither does
///     `is_single_static_assignment`, which demands EXACTLY ONE def and so
///     REJECTS every never-written parameter — the normal `requires` case —
///     while ACCEPTING a once-reassigned one — the unsound case):
///       - `local_is_never_written`: no `Assign` statement targets the formal
///         (`place_source_is_stable` alone tolerates ONE whole-local reassign,
///         e.g. `lo = lo + 1`, which invalidates the entry reading);
///       - `place_source_is_stable`: no slot-write channel (`&mut`, `&raw mut`,
///         `&raw const` of an owned place), projected store, projected call-dest,
///         set-discriminant, or deinit (the mutation
///         channels `local_is_never_written`'s whole-local scan cannot see);
///   * no Call terminator writes the formal (`lo = f(..)` is neither an `Assign`
///     statement nor >1 whole assign, so it slips BOTH predicates above).
pub(super) fn caller_precondition_var_is_entry_stable(
    func: &VerifiableFunction,
    name: &str,
) -> bool {
    // A FIELD-projected caller precondition (`self.0`, `self*.2`): admit it as a
    // stable hypothesis when its BASE parameter is entry-stable, reusing the exact
    // `param_place_is_entry_stable` discipline the overflow discharge uses. This
    // lets an honest caller (`length_sq`, `#[requires(|self.0| <= C)]`) use its own
    // field bound to discharge a callee's field precondition over the same field
    // (`self.dot(self)`).
    if let Some((base, suffix)) = split_projection_base(name) {
        return caller_precondition_field_base_is_entry_stable(func, base, suffix);
    }
    if name.starts_with('_') {
        return false;
    }
    let Some(decl) = crate::unique_named_local_decl(func, name) else {
        return false;
    };
    let local = decl.index;
    // A parameter is `1..=arg_count` (inlined `is_parameter`, which is
    // canonical-pipeline helper).
    if !(local >= 1 && local <= func.body.arg_count) {
        return false;
    }
    // A bare FLOAT formal's own `#[requires]` is the same entry fact the
    // Int/Bool cases carry (never-written + source-stable below guarantee the
    // read value IS the entry value; the guard lowering and ay's fp theory
    // handle the sort) — without it, a float callsite-precondition VC has NO
    // hypothesis about the caller's own bounded params and ay honestly refutes
    // a discharge the caller's contract in fact guarantees.
    if !matches!(decl.ty, Ty::Int { .. } | Ty::Bool | Ty::Float { .. }) {
        return false;
    }
    crate::fn_memo::collapse_to_bare(func, local, || {
        crate::local_is_never_written(func, local)
            && !local_has_call_dest_write(func, local)
            && crate::place_source_is_stable(func, local)
    })
}

/// True iff a caller `#[requires]` FIELD-projected var `<base><suffix>` denotes a
/// stable entry value: `base` names exactly one formal parameter and that
/// parameter is entry-stable (never field-written, `&mut`-borrowed, call-dest
/// written, set-discriminant'd, or deinit'd — `param_place_is_entry_stable`).
///
/// SOUNDNESS. The value read at a DIRECT field projection of an f64/scalar field
/// is a `Copy` leaf with no interior mutability, so once `param_place_is_entry_stable`
/// rules out every write / `&mut` aliasing channel to the base (including through a
/// `&mut` or by-value receiver's `(*self).i = …` store, whose `dest.local` is the
/// base), the field provably holds its entry value at every body read — exactly
/// the condition under which the entry `requires` fact remains true. `suffix` is
/// restricted to plain field-index / deref tokens (the substitution's `safe_suffix`
/// discipline); an index-by-var / downcast suffix is rejected fail-closed. A
/// `_`-prefixed or shadowed base is rejected (the `place_to_var_name` demotion
/// guarantee: an ambiguous source name is spelled `_<local>` in the body, so a
/// `self.0`-shaped fact could never bind a demoted base anyway).
pub(super) fn caller_precondition_field_base_is_entry_stable(
    func: &VerifiableFunction,
    base: &str,
    suffix: &str,
) -> bool {
    if suffix.is_empty() || !suffix.bytes().all(|b| b == b'.' || b == b'*' || b.is_ascii_digit()) {
        return false;
    }
    if base.starts_with('_') {
        return false;
    }
    // shadowed base name → ambiguous → fail-closed (`unique_named_local_decl` returns `None`)
    let Some(decl) = crate::unique_named_local_decl(func, base) else {
        return false;
    };
    let local = decl.index;
    if !(local >= 1 && local <= func.body.arg_count) {
        return false;
    }
    param_place_is_entry_stable(func, local)
}
