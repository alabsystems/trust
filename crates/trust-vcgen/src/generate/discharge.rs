// Generation paired with in-pass discharge, and the substitution machinery it
// needs: sigma actuals (the caller-side values bound to callee parameters),
// call fact tokens, and SSA version normalisation. The tokens must be spelled
// identically here and in the CHC lane or facts minted by one become inert in
// the other.

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
    let context = crate::VcgenContext::for_function(func.def_path.clone());
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
    box_deref_spans: &FxHashSet<SourceSpan>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    // verifier-perf: hold the mid-generation work-meter scope across BOTH the
    // `generate_vcs_impl` obligation walk AND the abstract-interp pre-pass below (both go
    // through owned `place_ty` queries). On the outermost entry this resets the
    // per-function meter; the nested `generate_vcs_impl` call shares one budget. If
    // anything here trips the budget the post-pass check below degrades the whole
    // function to Unknown. SOUNDNESS: DROP-ONLY.
    let _gen_work_scope = crate::gen_work_scope();

    let all_vcs = generate_vcs_impl(func, summaries, hardened, box_deref_spans);
    discharge_body_vcs(func, all_vcs)
}

/// The DISCHARGE + augment half of body VC generation: given the RAW
/// pre-discharge obligation set `all_vcs` from [`generate_vcs_impl`], classify
/// unsupported-MIR obligations, run the interval fixpoint, discharge what
/// interval analysis proves, and augment the rest with the abstract state.
///
/// Split out (from `generate_vcs_with_discharge_impl`) so the compiler's
/// VC-artifact cache can CACHE the raw `all_vcs` and re-run ONLY this
/// (dominant-cost-free: ~1-5% of generation) on a warm rebuild — re-minting the
/// interval proofs IN-PROCESS (no verdict replay) and re-augmenting with the
/// interval env (preserving provability).
///
/// Deterministic in `(func, all_vcs)` and PURE (no side effects beyond the work
/// meter). Does NOT open its own work scope — the caller owns the scope so the
/// combined path keeps its single-budget semantics byte-for-byte, and the
/// re-run path scopes it freshly (safe: the raw is cached only when the cold
/// run did NOT degrade, and discharge-alone work never re-trips the budget).
pub(super) fn discharge_body_vcs(
    func: &VerifiableFunction,
    all_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    if all_vcs.is_empty() {
        return (all_vcs, Vec::new());
    }

    let mut solver_candidates = Vec::with_capacity(all_vcs.len());
    let mut preclassified = Vec::new();
    for vc in all_vcs {
        let unsupported_reason = if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
            Some(format!("unsupported MIR `{kind}` preserved in TrustIr: {detail}"))
        } else {
            None
        };

        if let Some(reason) = unsupported_reason {
            preclassified.push((
                vc,
                VerificationResult::Unknown {
                    solver: Symbol::intern("trust_vcgen"),
                    time_ms: 0,
                    reason,
                },
            ));
        } else {
            solver_candidates.push(vc);
        }
    }

    if solver_candidates.is_empty() {
        return (Vec::new(), preclassified);
    }

    //, #452: Use type-aware initial state for tighter interval bounds,
    // then compute fixpoint with threshold widening, delayed widening, condition
    // narrowing, and descending narrowing for precision recovery.
    // Abstract interpretation also consumes `func.preconditions` directly;
    // give it the same arithmetic-safe view as VC construction.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let merged_env = abstract_interp::merged_interval_environment(arithmetic_safe_func.as_ref());

    // Discharge VCs that interval analysis can prove.
    let report = abstract_interp::try_discharge_batch(&solver_candidates, &merged_env);

    let discharged_map: FxHashMap<usize, VerificationResult> =
        report.discharged.into_iter().collect();
    let mut solver_vcs = Vec::new();
    let mut discharged = preclassified;
    for (i, vc) in solver_candidates.into_iter().enumerate() {
        if let Some(result) = discharged_map.get(&i) {
            discharged.push((vc, result.clone()));
        } else {
            // Augment remaining VCs with abstract-state assumptions
            // before solver dispatch. The abstract state is an over-approximation
            // of all concrete executions: adding its constraints as conjuncts to
            // the violation formula narrows the solver's search space without
            // excluding real counterexamples. If the environment is Top (no
            // finite bounds), the VC is returned unchanged.
            solver_vcs.push(abstract_interp::augment_vc_with_abstract_state(&vc, &merged_env));
        }
    }

    // verifier-perf (mid-generation work-bound): if the obligation walk or the
    // abstract-interp pre-pass tripped the per-function work budget, DISCARD everything
    // and degrade the whole function to a single fail-closed Unknown.
    // SOUNDNESS: DROP-ONLY — preclassifies to Unknown, never Proved.
    if crate::gen_work_tripped() {
        return gen_work_degraded_discharge(func);
    }

    (solver_vcs, discharged)
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
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    generate_vcs_with_discharge_and_summaries_configured_with_context(
        func, summaries, hardened, &context,
    )
}

/// Trust (box-deref doc-lint fix): the compiler passes the spans of
/// compiler-synthesized `Box` derefs so the always-`Bool(true)` missing-SAFETY
/// documentation lint is dropped for them (drop-only; see
/// `collect_synthesized_box_deref_spans` in the compiler). Generic over the
/// hasher so the compiler's `rustc_data_structures::fx::FxHashSet` (an alias for
/// the same `rustc_hash::FxHashSet`) passes through unchanged.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries_with_box_deref_spans<S: std::hash::BuildHasher>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    box_deref_spans: &std::collections::HashSet<SourceSpan, S>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_spans(
        func, summaries, false, &context, box_deref_spans,
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
    generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_spans(
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
/// `_with_box_deref_spans` variants above). Generic over the hasher so both
/// this crate's `FxHashSet` and the compiler's
/// `rustc_data_structures::fx::FxHashSet` alias pass through unchanged.
#[must_use]
pub fn generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_spans<
    S: std::hash::BuildHasher,
>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    context: &crate::VcgenContext,
    box_deref_spans: &std::collections::HashSet<SourceSpan, S>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let owned: FxHashSet<SourceSpan> = box_deref_spans.iter().cloned().collect();
    crate::with_function_vcgen_context(&func.def_path, context, || {
        generate_vcs_with_discharge_and_summaries_configured_impl(func, summaries, hardened, &owned)
    })
}

pub(super) fn generate_vcs_with_discharge_and_summaries_configured_impl(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    box_deref_spans: &FxHashSet<SourceSpan>,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    // This entry builds caller-side rows before it reaches `generate_vcs_impl`.
    // Admit the complete public body first so malformed positional MIR cannot
    // mint an otherwise-valid summary obligation alongside the later Unknown.
    if let Err(error) = crate::validate_function(func) {
        return preclassify_unsupported_mir_vcs(vec![malformed_trust_ir_vc(func, &error)]);
    }

    // verifier-perf: hold the mid-generation work-meter scope across the WHOLE outermost
    // entry — the callsite/guard-map machinery (`generate_callsite_precondition_vcs`) AND
    // the obligation walk (`generate_vcs_with_discharge`) both materialize declared types
    // via owned `place_ty` queries, so they must share ONE per-function budget.
    // Resets on this outermost 0→1 entry; the nested calls share it. SOUNDNESS:
    // DROP-ONLY.
    let _gen_work_scope = crate::gen_work_scope();

    let callsite_precondition_vcs = generate_callsite_precondition_vcs(func, summaries);

    // Body VCs are generated through the summary-aware lane: each proved callee's
    // postcondition is assumed (conjoined) at the dominated successors of its call,
    // so a downstream obligation that depends on the callee's guarantee can be
    // discharged instead of false-FAILing on a havoced result.
    let (mut solver_vcs, mut discharged) =
        generate_vcs_with_discharge_impl(func, Some(summaries), hardened, box_deref_spans);
    let (callsite_solver_vcs, callsite_preclassified) =
        preclassify_unsupported_mir_vcs(callsite_precondition_vcs);
    solver_vcs.extend(callsite_solver_vcs);
    discharged.extend(callsite_preclassified);

    // verifier-perf (mid-generation work-bound): if any sub-pass tripped the per-function
    // work budget, DISCARD all accumulated VCs and degrade the whole function to a single
    // fail-closed Unknown. SOUNDNESS: DROP-ONLY — Unknown, never Proved.
    if crate::gen_work_tripped() {
        return gen_work_degraded_discharge(func);
    }
    (solver_vcs, discharged)
}

/// Compiler VC-artifact-cache COLD-path variant: the `(solver_vcs, discharged)`
/// result is BYTE-IDENTICAL to
/// [`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_spans`]
/// (same single outermost work scope; the combined path's inner
/// `generate_vcs_with_discharge_impl` scope is share-only, so inlining the walk
/// + [`discharge_body_vcs`] here changes nothing) — PLUS the RAW pre-discharge
/// body obligation set for the cache.
///
/// `raw` is `Some(body_all_vcs)` ONLY when the result is fully reproducible from
/// that raw alone by [`discharge_captured_raw_body_with_context`]: the function
/// did not work-degrade, had body obligations, and emitted NO callsite-
/// precondition VCs (guaranteed when the summary DB is empty — the compiler's
/// cacheability precondition). Otherwise `None`, and the function is not cached.
#[must_use]
pub fn generate_vcs_capturing_raw_body_with_context<S: std::hash::BuildHasher>(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    hardened: bool,
    context: &crate::VcgenContext,
    box_deref_spans: &std::collections::HashSet<SourceSpan, S>,
) -> (
    Vec<VerificationCondition>,
    Vec<(VerificationCondition, VerificationResult)>,
    Option<Vec<VerificationCondition>>,
) {
    let owned: FxHashSet<SourceSpan> = box_deref_spans.iter().cloned().collect();
    crate::with_function_vcgen_context(&func.def_path, context, || {
        let _gen_work_scope = crate::gen_work_scope();
        let callsite_precondition_vcs = generate_callsite_precondition_vcs(func, summaries);
        let callsite_empty = callsite_precondition_vcs.is_empty();
        // Body obligation WALK — the cacheable raw set (~95-99% of generation).
        let body_all_vcs = generate_vcs_impl(func, Some(summaries), hardened, &owned);
        let raw_capture = body_all_vcs.clone();
        // Body DISCHARGE + augment (shares this scope; ~1-5% of generation).
        let (mut solver_vcs, mut discharged) = discharge_body_vcs(func, body_all_vcs);
        let (callsite_solver_vcs, callsite_preclassified) =
            preclassify_unsupported_mir_vcs(callsite_precondition_vcs);
        solver_vcs.extend(callsite_solver_vcs);
        discharged.extend(callsite_preclassified);
        if crate::gen_work_tripped() {
            let (s, d) = gen_work_degraded_discharge(func);
            return (s, d, None);
        }
        let raw = if raw_capture.is_empty() || !callsite_empty {
            None
        } else {
            Some(raw_capture)
        };
        (solver_vcs, discharged, raw)
    })
}

/// Prospective measurement-only rehydration helper: re-run body
/// discharge+augment on a previously captured raw obligation set, re-minting
/// the interval proofs in-process (no verdict is replayed from storage).
///
/// The `(solver_vcs, discharged)` result equals the cold generation's whenever
/// `raw_body` is a set that [`generate_vcs_capturing_raw_body_with_context`]
/// returned as `Some` (non-degraded, empty callsite).
///
/// This helper is not a compiler verdict path and does not authorize a cache
/// hit to replace fresh VC generation. It is public only so measurement and
/// parity tests can evaluate a possible future split. Any future compiler use
/// requires its own complete cache-key and obligation-completeness design,
/// authority review, and fail-closed regression battery.
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
    let mut solver_vcs = Vec::new();
    let mut preclassified = Vec::new();
    for vc in vcs {
        let unsupported_reason = if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
            Some(format!("unsupported MIR `{kind}` preserved in TrustIr: {detail}"))
        } else {
            None
        };

        if let Some(reason) = unsupported_reason {
            preclassified.push((
                vc,
                VerificationResult::Unknown {
                    solver: Symbol::intern("trust_vcgen"),
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
/// opaque symbol — every `OpaqueScalar` of a given width collapses to one
/// `__trust_opaque_scalar_uN`, every other unknown const to one `__unknown_const`. Two DISTINCT
/// such actuals bound to two DISTINCT callee parameters would then SHARE one symbol, which
/// silently asserts `param_i == param_j` and can turn a satisfiable `¬P[σ]` into a spurious
/// UNSAT — a FALSE discharge (e.g. `helper(M, N)` with inferred `P = a >= b` over const generics
/// `M, N` would certify `¬(S >= S)` UNSAT and "prove" a violable subtraction). The `OpaqueScalar`
/// model invariant requires each occurrence to be an INDEPENDENT fresh symbol; honor it here by
/// re-keying every opaque/unknown actual on its formal, so distinct callee parameters never
/// alias. Strictly weaker than the truth, never falsely proves; concrete actuals (ints, bools,
/// strings — already injective) are untouched, so genuine discharges (e.g. a constant divisor)
/// are unaffected.
pub(super) fn sigma_actual_formula(func: &VerifiableFunction, formal: &str, actual: &Operand) -> Formula {
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
    // `place_source_is_stable` (single assignment, no `&mut`/`&raw mut`, no projected
    // or call-dest store, no set-discriminant/deinit), so the temp provably holds the
    // root's unchanged value at the call. A stale-guard vector (`x` reborrowed `&mut`
    // and reassigned before the call) fails `place_source_is_stable` at the root, so
    // σ falls back to the opaque `_6` name and the guard does NOT discharge
    // (fail-closed). Adding the true equality `_6 == x` only REMOVES freedom from the
    // obligation, so it can turn a false-FAIL into a PROVE for a genuine guard but can
    // never mask a real out-of-bounds (a too-weak/off-by-one/other-var guard stays
    // SAT and still fails).
    if let Some(root) = sigma_actual_stable_copy_root(func, actual) {
        return operand_to_formula(func, &Operand::Copy(root));
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
///     (`unique_whole_local_def`) — or a UNIQUE whole-local `Rvalue::Cast` whose
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
pub(super) fn sigma_actual_stable_copy_root(func: &VerifiableFunction, actual: &Operand) -> Option<Place> {
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
        seen += 1;
        if seen > 16 {
            return None;
        }
        match crate::unique_whole_local_def(func, local) {
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
    // The root must hold a SINGLE FIXED value for the whole body — the entry value of
    // a parameter, unchanged — so the temp provably equals it at the call and the
    // guard's same-named read denotes the same value. Three independent gates, all
    // required:
    //   * `local_is_never_written`: NO assignment statement rewrites the root (a
    //     parameter reassigned even once — `x = x + 1` — has `place_source_is_stable`
    //     `whole_assigns == 1 <= 1` = true, yet its value changed from the entry
    //     value the guard/σ name `x` denotes; this gate rejects it). A never-written
    //     non-parameter local has no value at all and is likewise excluded.
    //   * `place_source_is_stable`: no `&mut`/`&raw mut` borrow, projected store,
    //     set-discriminant, or deinit reseats/mutates it (the stale-guard `&mut`
    //     vector).
    //   * `local_has_call_dest_write`: NEITHER of the above sees a whole-local
    //     CALL-destination reassign of a PARAMETER (`x = f(..)`):
    //     `local_is_never_written` scans only statements, and
    //     `place_source_is_stable` counts it as the single permitted
    //     `whole_assigns` because a parameter's entry binding is not an explicit
    //     store. Without this gate the fold would equate the temp with a root
    //     whose value CHANGED since entry — one SMT name for two values, a false-
    //     discharge channel. Explicit reject, fail-closed.
    // Together they guarantee the root denotes its fixed entry value at every read.
    if !crate::local_is_never_written(func, local)
        || !crate::place_source_is_stable(func, local)
        || local_has_call_dest_write(func, local)
    {
        return None;
    }
    let root = Place { local, projections: Vec::new() };
    // Require a source-named, UNIQUELY-named root: otherwise `place_to_var_name`
    // falls back to `_{local}`, which does NOT match the guard's source-name read,
    // so the fold would not help (and could, for a shadowed name, mis-key a fact).
    let name = func.body.locals.get(local).and_then(|d| d.name.as_deref())?;
    if name.starts_with('_') {
        return None;
    }
    if func.body.locals.iter().filter(|d| d.name.as_deref() == Some(name)).count() != 1 {
        return None;
    }
    Some(root)
}

/// A whole-or-projected CALL-destination write to `local` anywhere in the body.
/// Complements `local_is_never_written` (statement assigns only — call dests are
/// terminators) and `place_source_is_stable` (which admits ONE whole-local
/// call-dest store, the entry construction slot a PARAMETER never uses). Used by
/// stability gates that must mean "the local's value is its entry value at every
/// read".
pub(super) fn local_has_call_dest_write(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().any(
        |block| matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local),
    )
}

/// Trust (piece #8 — σ length-rendering): the LENGTH of the ACTUAL slice/array
/// argument `actual` passed at a call site, for the caller `func`, when it can be
/// rendered EXACTLY and STABLY. Returns `Some(len_formula)` only for the three
/// sound sources; anything else returns `None` and the caller emits no length
/// replacement (the callee's `<formal>__slice_len` stays a free var ⇒ `¬P[σ]`
/// SAT ⇒ fail-closed, INV-2).
///
///   * (c) `actual` is a PARAMETER-slice reborrow (`fill(s, k)` on `s: &mut [T]`):
///     `param_slice_len` resolves it to the caller's own `s__slice_len`, tied to
///     the caller's fat-pointer metadata. The caller's guard `k <= s.len()`
///     discharges `¬(k <= s__slice_len)` through the existing guard machinery.
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
pub(super) fn sigma_actual_slice_len(func: &VerifiableFunction, actual: &Operand) -> Option<Formula> {
    const TRACE_FUEL: u32 = 16;
    // (c) A parameter-slice reborrow → the caller's own `<param>__slice_len`.
    if let Some(len) = param_slice_len(func, actual, TRACE_FUEL) {
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
    if !p.projections.is_empty() {
        return None;
    }
    match crate::unique_whole_local_def(func, p.local)? {
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
pub(super) fn local_versions_collapse_to_bare(func: &VerifiableFunction, local: usize) -> bool {
    let is_param = (1..=func.body.arg_count).contains(&local);
    if is_param {
        crate::local_is_never_written(func, local)
            && !local_has_call_dest_write(func, local)
            && crate::place_source_is_stable(func, local)
    } else {
        is_single_static_assignment(func, local)
    }
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
pub(super) fn bare_ssa_guard_variant(func: &VerifiableFunction, guard: &Formula) -> Option<Formula> {
    let mut renames: Vec<(String, Formula)> = Vec::new();
    guard.visit(&mut |f| {
        if let Formula::Var(name, sort) = f
            && let Some((base, _tok)) = name.split_once('#')
            && !renames.iter().any(|(n, _)| n == name)
        {
            let base_local = (0..func.body.locals.len()).find(|&l| {
                crate::place_to_var_name(func, &Place { local: l, projections: Vec::new() }) == base
            });
            if let Some(local) = base_local
                && local_versions_collapse_to_bare(func, local)
            {
                renames.push((name.clone(), Formula::var_owned(base.to_string(), sort.clone())));
            }
        }
    });
    if renames.is_empty() {
        return None;
    }
    Some(substitute_summary_params(guard, &renames))
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
pub(super) fn normalize_ssa_version_tokens(func: &VerifiableFunction, formula: &Formula) -> Formula {
    let mut renames: Vec<(String, Formula)> = Vec::new();
    formula.visit(&mut |f| {
        if let Formula::Var(name, sort) = f
            && let Some((base, _tok)) = name.split_once('#')
            && !renames.iter().any(|(n, _)| n == name)
        {
            let base_local = (0..func.body.locals.len()).find(|&l| {
                crate::place_to_var_name(func, &Place { local: l, projections: Vec::new() }) == base
            });
            if let Some(local) = base_local
                && local_versions_collapse_to_bare(func, local)
            {
                renames.push((name.clone(), Formula::var_owned(base.to_string(), sort.clone())));
            }
        }
    });
    if renames.is_empty() {
        return formula.clone();
    }
    substitute_summary_params(formula, &renames)
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

/// True for the two by-NAME-interned opaque symbols `operand_to_formula` produces for
/// alias-prone consts: `__trust_opaque_scalar_{u,i}{width}` (OpaqueScalar) and `__unknown_const`
/// (the unevaluated/unknown fallback). NOT the σ namespace `__trust_sigma_opaque__*`, which is
/// already per-formal-distinct (`sigma_actual_formula`) and must be left intact so `¬P[σ]`
/// remains structurally equal to `¬substituted` for the discharge gate.
pub(super) fn is_aliasing_opaque_symbol_name(name: &str) -> bool {
    // The COMPLETE set of by-name-interned opaque/unknown symbols (enumerated against
    // operand_to_formula, lib.rs ~2150-2214) — each keyed only by width/type/kind, never by
    // value, so two distinct values collapse onto one symbol:
    //   __trust_opaque_scalar_{u,i}{width}  integer const-generic / assoc-const / size_of
    //   __unknown_const                     unevaluated/unknown ConstValue fallback
    //   __trust_unsupported_operand_{k}_{d} non-int/bool/Alias const refused by convert.rs, keyed
    //                                       by type ⇒ distinct bool/projection values collide
    //   __unknown_operand                   unknown-Operand fallback
    // EXCLUDED (injective, must NOT be freshened): __trust_float_bits_* (by bits), Str (by bytes),
    // __trust_callable_reify_{dest} (by dest), plain places `_n`, and the σ namespace
    // __trust_sigma_opaque__* (already per-formal-distinct; freshening it would break
    // `¬P[σ] == ¬substituted` at the discharge gate).
    //   __trust_constparam_{index}_{name}   const-generic PARAM value / array length (piece #7a)
    name.starts_with("__trust_opaque_scalar_")
        || name == "__unknown_const"
        || name.starts_with("__trust_unsupported_operand_")
        || name == "__unknown_operand"
        // Trust: piece #7a — a const-generic PARAM value shares one symbol WITHIN
        // a function (the guard `N` and the array length `N` must be the SAME term
        // — this is the intra-function tie, and freshen does NOT run on that path).
        // But on the R1 σ callsite path, a const-param actual flowing to TWO callee
        // params must NOT alias — exactly the OpaqueScalar M==N hazard. So it must
        // be freshened per occurrence there. Registering the family here is both
        // correct AND necessary (without it, `helper(M, N)` could re-introduce the
        // M==N alias on the σ path). Sound: freshening only splits distinct
        // occurrences apart; it never merges.
        || name.starts_with("__trust_constparam_")
}

/// Per-OCCURRENCE freshen every alias-prone opaque symbol leaf in `formula`.
///
/// SOUNDNESS (R1 caller-propagation, complete alias fix): const-generic / associated-const /
/// unevaluated-const operands lower (in `operand_to_formula`) to a single by-name-interned
/// symbol per `(width,signed)`, so two DISTINCT such values collapse to ONE symbol and silently
/// assert an equality between unrelated terms. The σ-substitution surface is fixed locally
/// (`sigma_actual_formula`), but the SAME interned symbol re-enters the discharge obligation as a
/// SUB-operand through many guard/semantic-fact helpers (bool-temp resolution, the BinaryOp/Cast
/// semantic arms, checked-arith results, min/max/clamp facts). Rather than chase every syntactic
/// site, this single structural post-pass over the FINAL obligation gives every such leaf an
/// INDEPENDENT fresh name (`{name}__r1occ{n}`), honoring the `OpaqueScalar` model invariant
/// ("each occurrence an independent fresh symbol"). Splitting a shared symbol only REMOVES
/// implied equalities ⇒ the obligation can only move SAT-ward ⇒ `certify_vc`'s UNSAT (discharge)
/// set strictly shrinks ⇒ a previously-false discharge is killed, a genuine one is preserved.
/// The opaque arms always mint `Sort::Int`, so the fresh leaf keeps that sort.
pub(super) fn freshen_aliasing_opaque_occurrences(
    formula: &Formula,
    counter: &std::cell::Cell<u32>,
) -> Formula {
    if let Some(name) = formula.var_name()
        && is_aliasing_opaque_symbol_name(name)
    {
        let n = counter.get();
        counter.set(n + 1);
        return Formula::var_owned(format!("{name}__r1occ{n}"), Sort::Int);
    }
    formula.clone().map_children(&mut |child| freshen_aliasing_opaque_occurrences(&child, counter))
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
            pre.free_variables()
                .iter()
                .all(|name| caller_precondition_var_is_entry_stable(func, name))
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
///       - `place_source_is_stable`: no `&mut`/`&raw mut` escape, projected
///         store, projected call-dest, set-discriminant, or deinit (the mutation
///         channels `local_is_never_written`'s whole-local scan cannot see);
///   * no Call terminator writes the formal (`lo = f(..)` is neither an `Assign`
///     statement nor >1 whole assign, so it slips BOTH predicates above).
pub(super) fn caller_precondition_var_is_entry_stable(func: &VerifiableFunction, name: &str) -> bool {
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
    let mut named = func.body.locals.iter().filter(|d| d.name.as_deref() == Some(name));
    let Some(decl) = named.next() else {
        return false;
    };
    if named.next().is_some() {
        return false;
    }
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
    if !crate::local_is_never_written(func, local) || !crate::place_source_is_stable(func, local) {
        return false;
    }
    !func
        .body
        .blocks
        .iter()
        .any(|b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == local))
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
    let mut named = func.body.locals.iter().filter(|d| d.name.as_deref() == Some(base));
    let Some(decl) = named.next() else {
        return false;
    };
    if named.next().is_some() {
        return false; // shadowed base name → ambiguous → fail-closed
    }
    let local = decl.index;
    if !(local >= 1 && local <= func.body.arg_count) {
        return false;
    }
    param_place_is_entry_stable(func, local)
}
