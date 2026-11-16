//! Final-artifact calculus reporting. Pending computation is NOT proof,
//! caller/optimizer authority or permission to omit a row. The original
//! publisher judges every fallback, including a missing final module.

use super::*;

// Bulk publication data lives in one exclusively owned descriptor, not in
// full per-body verification carriers. The prepare/emit conversion below is
// still being completed before any production base pin may be enabled.
mod spool;
mod model_coverage;
mod diagnostic_data;
mod native_debt;
pub(super) mod publication_output;
pub(super) mod publication_errors;
mod prepared;
mod publication_identity;
mod stored;
mod proposal;
mod selection;

#[derive(Clone)]
pub(super) struct Computation {
    deadline: Option<std::time::Instant>,
    credit: trust_types::verify_budget::ClockCreditMark,
}

pub(super) fn capture_inputs(
    deadline: Option<std::time::Instant>,
    actual_native_bundle_complete: bool,
) -> Option<Computation> {
    // Flag/pin-off allocates no hint snapshot or reporting record. The bool is
    // supplied only at the actual final Ok(Some(native bundle)) construction,
    // never inferred from public root-row labels or diagnostic text.
    if !trust_certify::calculus_row::base::has_production_pin()
        || !actual_native_bundle_complete
        || trust_types::verify_budget::exhausted_readonly()
    {
        return None;
    }
    Some(Computation {
        deadline,
        credit: trust_types::verify_budget::clock_credit_mark(),
    })
}

pub(super) fn finish_inputs(artifacts: &mut VerificationArtifacts, deadline: Option<std::time::Instant>) {
    if let Some(input) = artifacts.calculus_reporting.as_mut() {
        input.deadline = trust_types::verify_budget::earliest(
            trust_types::verify_budget::credited(input.deadline, input.credit),
            trust_types::verify_budget::earliest(
                deadline,
                trust_types::verify_budget::current_deadline(),
            ),
        );
        input.credit = trust_types::verify_budget::clock_credit_mark();
        if trust_types::verify_budget::exhausted_readonly() {
            artifacts.calculus_reporting = None;
        }
    }
}

#[derive(Default, PartialEq, Eq)]
enum Phase {
    #[default]
    Collecting,
    Finalizing,
    Closed,
}

struct PendingBody {
    func_path: String,
    def_path: String,
    span: rustc_span::Span,
    sequence: u64,
    publication: stored::StoredPublication,
    clock: Option<PendingClock>,
    duplicate: bool,
}

/// The owning function's guard has already returned when a report is held.
/// Only OTHER function scopes completed after this mark earn clock credit.
/// Thread-local credit is never transferred across worker threads, and an
/// inherited ambient bound remains an absolute stop rather than renewable
/// per-body time. No clock is reset to `now + budget`.
pub(super) struct PendingClock {
    deadline: Option<std::time::Instant>,
    hard_deadline: Option<std::time::Instant>,
    credit: trust_types::verify_budget::ClockCreditMark,
    owner: std::thread::ThreadId,
}

pub(super) fn capture_publication_clock(
    tcx: TyCtxt<'_>,
    artifacts: &VerificationArtifacts,
) -> Option<PendingClock> {
    if !trust_certify::calculus_row::base::has_production_pin()
        || !tcx.sess.trust_ir_lower_enabled()
    {
        return None;
    }
    let input = artifacts.calculus_reporting.as_ref()?;
    if !tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        state.phase == Phase::Collecting && state.approved.is_some()
    }) {
        return None;
    }
    PendingClock::capture(input.deadline)
}

impl PendingClock {
    fn capture(deadline: Option<std::time::Instant>) -> Option<Self> {
        let hard_deadline = trust_types::verify_budget::current_deadline();
        if trust_types::verify_budget::exhausted_readonly()
            || trust_types::verify_budget::earliest(deadline, hard_deadline)
                .is_some_and(|at| std::time::Instant::now() >= at)
        {
            return None;
        }
        Some(Self {
            deadline,
            hard_deadline,
            credit: trust_types::verify_budget::clock_credit_mark(),
            owner: std::thread::current().id(),
        })
    }

    fn deadline(&self) -> Result<Option<std::time::Instant>, ()> {
        if self.owner != std::thread::current().id() { return Err(()); }
        Ok(trust_types::verify_budget::earliest(
            trust_types::verify_budget::credited(self.deadline, self.credit),
            trust_types::verify_budget::earliest(
                self.hard_deadline, trust_types::verify_budget::current_deadline(),
            ),
        ))
    }
}

#[derive(Default)]
struct Reporting {
    attempted_base: bool,
    source_coverage: Option<model_coverage::SourceCoverage>,
    approved: Option<Arc<trust_certify::calculus_row::hints::Vf5HintSession>>,
    phase: Phase,
    bodies: FxHashMap<ArtifactCacheKey, PendingBody>,
    preparing: FxHashSet<ArtifactCacheKey>,
    duplicate_keys: FxHashSet<ArtifactCacheKey>,
    next_sequence: u64,
    storage: Option<Arc<spool::PublicationSpool>>,
    inventory: Option<FxHashSet<LocalDefId>>,
}

/// Prepare one immutable mathematical base before the analysis seam can
/// demand any per-body verifier. Its fixed replay limits and any genuine
/// inherited stop apply here; setup earns no function-clock credit.
pub(super) fn initialize(tcx: TyCtxt<'_>) {
    if !verification_enabled(tcx.sess)
        || !trust_certify::calculus_row::base::has_production_pin()
        || !tcx.sess.trust_ir_lower_enabled()
    {
        return;
    }
    let Some(root) = tcx.sess.opts.unstable_opts.trust_proof_artifact_root.as_deref() else {
        return;
    };
    let prepare = tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        if state.phase != Phase::Collecting || state.attempted_base {
            return false;
        }
        state.attempted_base = true;
        true
    });
    if !prepare {
        return;
    }
    let source_coverage = match model_coverage::SourceCoverage::capture(tcx) {
        Ok(coverage) => coverage,
        Err(error) => {
            debug!("VF5 source outside pinned model; ordinary policy remains: {error:?}");
            return;
        }
    };
    // This is a fixed mathematical resource of the selected sysroot. Neither
    // a row hint nor an environment variable selects a different base/pin.
    let package = tcx.sess.opts.sysroot.path().join("lib/trust/vf5-base-v1");
    let approved = match trust_certify::calculus_row::Vf5Reference::load_package_until(
        &package, trust_types::verify_budget::current_deadline(),
    ) {
        Ok((reference, _report)) => {
            trust_certify::calculus_row::hints::Vf5HintSession::new(reference, root)
                .map(Arc::new)
                .map_err(|error| debug!("VF5 hint session unavailable; ordinary policy remains: {error:?}"))
                .ok()
        }
        Err(error) => {
            debug!("VF5 base unavailable; ordinary policy remains: {error:?}");
            None
        }
    };
    let storage = approved.as_ref().and_then(|_| {
        spool::PublicationSpool::create(root)
            .map_err(|error| debug!("VF5 publication storage unavailable: {error}; ordinary policy remains"))
            .ok()
    });
    tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        if state.phase == Phase::Collecting {
            state.source_coverage = Some(source_coverage);
            state.approved = approved;
            state.storage = storage;
        }
    });
}

fn candidates(artifacts: &VerificationArtifacts, overflow_checks: bool, deadline: Option<std::time::Instant>) -> Option<Vec<ExactResultRowIdentity>> {
    artifacts.calculus_reporting.as_ref()?;
    if deadline.is_some_and(|at| std::time::Instant::now() >= at)
        || artifacts.results.len() != artifacts.result_bindings.len()
        || artifacts.results.len() != artifacts.proof_authorities.len()
        || artifacts.results.iter().any(|(vc, result)| {
            matches!(result, VerificationResult::Failed { .. } | VerificationResult::Timeout { .. })
                || result_is_held_assert_refutation(result)
                || matches!(vc.kind, VcKind::UnsupportedMir { .. })
        })
    {
        return None;
    }
    let run = artifacts.full_verification.as_ref()?;
    let summary = &run.summary;
    if native_run_trust_ir_lowering_failed(run)
        || summary.failed != 0 || summary.timed_out != 0 || summary.cancelled != 0
        || summary.unsupported != 0 || summary.skipped != 0
        || summary.missing_proof_artifacts != 0 || summary.publication_conflicts != 0
        || !run.skipped.is_empty()
    {
        return None;
    }
    let mut rows = Vec::new();
    for (index, (vc, result)) in artifacts.results.iter().enumerate() {
        if !calculus_row_covers(vc, overflow_checks) || artifacts.proof_authorities[index].is_some() {
            continue;
        }
        if !matches!(result, VerificationResult::Unknown { .. } | VerificationResult::Proved { .. }) {
            return None;
        }
        let binding = artifacts.result_bindings[index].as_ref()?;
        if !binding.matches_row(index, vc) {
            return None;
        }
        rows.push(exact_result_row_identity(index, vc)?);
    }
    (!rows.is_empty()).then_some(rows)
}

pub(super) fn defer<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
    artifacts: &Arc<VerificationArtifacts>,
    policy: &TrustVerifyPolicy,
    dispatch: &mut Option<OpenDispatchRefutationWitnesses>,
    errors_before_publish: publication_errors::OriginalErrorBaseline,
    clock: Option<PendingClock>,
) -> bool {
    if !trust_certify::calculus_row::base::has_production_pin()
        || !tcx.sess.trust_ir_lower_enabled()
    {
        return false;
    }
    // The existing session/body key distinguishes promoted/closure/shim
    // sources too. Original-only failures keep their full population; only a
    // later checked alternative will require a concrete supported function.
    let key = artifact_cache_key_with_def_path(tcx, body, policy, func_path);
    let admission = tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        if state.phase != Phase::Collecting || state.approved.is_none() {
            return None;
        }
        if state.preparing.contains(&key) || state.bodies.contains_key(&key) {
            state.duplicate_keys.insert(key.clone());
            return Some(Err(()));
        }
        let storage = Arc::clone(state.storage.as_ref()?);
        let sequence = state.next_sequence;
        state.next_sequence = sequence.checked_add(1)?;
        state.preparing.insert(key.clone());
        Some(Ok((storage, sequence)))
    });
    let Some(admission) = admission else { return false };
    let (storage, sequence) = match admission {
        Ok(admission) => admission,
        Err(()) => {
            tcx.dcx().err(format!("VF5 publication received a duplicate original carrier for {func_path}"));
            return false;
        }
    };
    let def_path = with_no_trimmed_paths!(tcx.def_path_str(body.source.def_id()));
    let prepared_dispatch = dispatch.take().expect("admitted original publisher owns its dispatch facts");
    let mut output = prepared::CollectedPublication::new(clock.as_ref());
    // ALL original policy/source/private ledger work happens HERE, while the
    // real body/context/native carriers and original row-key guard still live.
    // The final barrier emits DATA only; it never demands optimized_mir again.
    run_body_publication(
        tcx, body, func_path, artifacts, policy, &prepared_dispatch,
        errors_before_publish, &mut output,
    );
    let saved = match output.finish() {
        None => None, // Exact original prefix/rest was already emitted once.
        Some(mut original) => {
            let local = body.source.def_id().as_local();
            let can_propose = body.source.promoted.is_none()
                && matches!(body.source.instance, ty::InstanceKind::Item(_))
                && local.is_some_and(|local| {
                    matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn)
                        && !tcx.generics_of(local).requires_monomorphization(tcx)
                });
            let rows = can_propose.then(|| {
                let clock = clock.as_ref()?;
                candidates(artifacts, tcx.sess.overflow_checks(), clock.deadline().ok()?)
            }).flatten();
            let proposed = rows.as_ref().and_then(|rows| {
                proposal::prepare(tcx.sess, &original, artifacts, rows, clock.as_ref()?)
            });
            let saved = if let Some(proposed) = proposed {
                match stored::save_pair(&storage, &key, &original, proposed) {
                    Ok((saved, proposed, spans)) => {
                        let owed = original.owed.take().expect("sealed original retains its complete inventory");
                        Ok(stored::finish_saved_pair(saved, proposed, spans, owed))
                    }
                    Err(error) => Err((error, original)),
                }
            } else {
                stored::save_original(&storage, &key, original)
                    .map(stored::StoredPublication::Original)
            };
            match saved {
                Ok(publication) => Some(publication),
                Err((error, original)) => {
                    debug!("VF5 DATA admission refused: {error}; same original output remains");
                    original.emit_original(tcx);
                    None
                }
            }
        }
    };
    let mut record = saved.map(|publication| PendingBody {
        func_path: func_path.to_owned(), def_path, span: body.span,
        sequence, publication, clock, duplicate: false,
    });
    tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        state.preparing.remove(&key);
        if state.phase == Phase::Collecting && let Some(mut pending) = record.take() {
            pending.duplicate = state.duplicate_keys.remove(&key);
            state.bodies.insert(key.clone(), pending);
        }
    });
    if let Some(record) = record {
        // A reentrant barrier cannot orphan an in-flight original report.
        emit_original_record(tcx, &key, record);
    }
    true
}

pub(super) fn retain_inventory(tcx: TyCtxt<'_>, eligible: &FxHashSet<LocalDefId>) -> bool {
    if !trust_certify::calculus_row::base::has_production_pin() {
        return false;
    }
    tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        if state.bodies.is_empty() {
            return false;
        }
        state.inventory = Some(eligible.clone());
        true
    })
}

/// Called only at the two interface barrier sites. Existing errors force
/// original-policy fallback before the unchanged fatal gate. Success reads
/// the real final published module before any codegen or terminal summary.
pub(super) fn finalize(tcx: TyCtxt<'_>, allow_proofs: bool) {
    if !trust_certify::calculus_row::base::has_production_pin() {
        return;
    }
    let (mut pending, inventory, incomplete, approved, coverage) = tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        if state.phase != Phase::Collecting {
            return (Vec::new(), None, false, None, None);
        }
        state.phase = Phase::Finalizing;
        let incomplete = !state.preparing.is_empty();
        // Draining only transfers owned DATA. The pre-sort `any` below reads
        // booleans without queries; emission then follows each record's unique,
        // checked admission sequence, never this hash-map traversal order.
        #[allow(rustc::potential_query_instability)]
        let bodies = state.bodies.drain().collect::<Vec<_>>();
        (bodies, state.inventory.take(), incomplete,
            state.approved.take(), state.source_coverage.take())
    });
    if incomplete {
        tcx.dcx().err("VF5 final publication reached an in-flight original body; proof selection refused");
    }
    // Admission is for this ONE actual immutable final module, not one full
    // module rescan per body. Row proofs themselves are never cached here.
    let final_artifact = if allow_proofs && !incomplete
        && pending.iter().any(|(_, record)| {
            !record.duplicate && record.clock.is_some() && record.publication.has_proposal()
        })
    {
        coverage.and_then(|coverage| coverage.capture_final(tcx))
    } else {
        None
    };
    pending.sort_by_key(|(_, record)| record.sequence);
    for (key, record) in pending {
        emit_record(tcx, &key, record, final_artifact.as_ref(), approved.as_deref());
    }
    tcx.sess.with_trust_compiler_state::<Reporting, _>(|state| {
        state.phase = Phase::Closed;
        // All emitted handles have consumed their committed data. Closing the
        // phase releases the anonymous backing file and session-only math base;
        // neither is caller/optimizer authority needed by subsequent codegen.
        state.storage = None;
        state.approved = None;
        state.source_coverage = None;
    });
    if let Some(eligible) = inventory {
        let policy = TrustVerifyPolicy::from_session(tcx.sess);
        let audit = elide_audit::CrateScope::enter(tcx, "crate:finalize");
        finish_verification_inventory(tcx, &policy, eligible, audit);
    }
}

fn emit_original_record(tcx: TyCtxt<'_>, key: &str, record: PendingBody) {
    emit_record(tcx, key, record, None, None);
}

fn emit_record(
    tcx: TyCtxt<'_>,
    key: &str,
    record: PendingBody,
    final_artifact: Option<&model_coverage::FinalArtifact>,
    approved: Option<&trust_certify::calculus_row::hints::Vf5HintSession>,
) {
    if record.duplicate {
        tcx.dcx().err(format!("VF5 publication received duplicate original carriers for {}", record.func_path));
    }
    let current = || {
        !record.duplicate && final_artifact.is_some() && approved.is_some()
            && trust_certify::calculus_row::base::preparation_stop().is_none()
            && record.clock.as_ref().is_some_and(|clock| {
                clock.deadline().is_ok_and(report_deadline_allows)
            })
    };
    match record.publication.restore(key, current) {
        Ok(mut restored) => {
            let selected = (|| {
                let delta = restored.proposed.take()?;
                if !current() { return None; }
                let claim = final_artifact?.claim(&record.def_path)?;
                if !current() { return None; }
                let deadline = record.clock.as_ref()?.deadline().ok()?;
                let checked = approved?.replay(&claim, deadline)
                    .map_err(|error| debug!("VF5 final replay missed for {}: {error:?}; original policy remains", record.func_path))
                    .ok()?;
                selection::apply(&mut restored.original, delta, &checked, &claim, current)
            })();
            if let Some(selected) = selected {
                restored.original.emit_selected(tcx, selected);
            } else {
                restored.original.emit_original(tcx);
            }
        }
        Err((error, owed)) => {
            // A one-consume read refusal keeps the entire original denominator
            // explicitly owed. Never mint an empty success or retry storage.
            let mut diagnostic = tcx.dcx().struct_span_err(record.span, format!(
                "Trust could not restore the original verification report for `{}`: {error}",
                record.func_path,
            ));
            diagnostic.note(format!(
                "{} original row identities remain owed (inventory SHA-256 {:02x?}); no replacement proof or successful empty report was published",
                owed.total(), owed.digest(),
            ));
            diagnostic.emit();
        }
    }
}

// Production base pins remain EMPTY. These implementation checkpoints are
// UNCOMPILED and claim no operational VF5/CORE3 completion until independently
// measured base pins and genuine changed-source qualification are complete.

pub(super) fn report_deadline_allows(deadline: Option<std::time::Instant>) -> bool {
    !trust_types::verify_budget::exhausted_readonly()
        && !deadline.is_some_and(|at| std::time::Instant::now() >= at)
        && clean_kernel::tc::run_until(None, clean_kernel::tc::poll_deadline).is_some()
}

/// A late calculus proof changes exactly its sealed rows. Every unrelated
/// disposition, fingerprint and named premise remains the eager carrier's
/// value, including source-derived definition-entry classification. Retaining
/// or re-extracting the full source function is neither necessary nor allowed.
#[cfg(test)]
pub(super) fn project_calculus_dispositions(
    original: &TrustProofResults,
    results: &[(VerificationCondition, VerificationResult)],
    bindings: &[Option<ResultObligationBinding>],
    authorities: &[Option<ResultProofAuthority>],
    minted: &[usize],
) -> Option<TrustProofResults> {
    if !original.has_aligned_obligation_arrays()
        || original.dispositions.len() != results.len()
        || bindings.len() != results.len() || authorities.len() != results.len()
    {
        return None;
    }
    let mut projected = original.clone();
    let mut seen = FxHashSet::default();
    for &index in minted {
        let id = ObligationId::from_usize(index);
        let (vc, result) = results.get(index)?;
        let authority = authorities[index].as_ref()?;
        if !seen.insert(index)
            || !matches!(authority, ResultProofAuthority::CalculusRowProved { .. })
            || original.premises.iter().any(|premise| premise.obligation == id)
        {
            return None;
        }
        let (status, strength) = trust_disposition_for_authority(
            Some(authority), index, vc, result, bindings[index].as_ref(),
        )?;
        if status != TrustStatus::Trusted || strength != TrustProofStrength::Constructive {
            return None;
        }
        let disposition = projected.dispositions.get_mut(id)?;
        if disposition.kind != convert_vc_kind(&vc.kind) {
            return None;
        }
        *disposition = TrustDisposition { kind: disposition.kind, status, strength, certified: false };
    }
    projected.summary = TrustFunctionSummary::from_dispositions(&projected.dispositions);
    // Row kinds did not change, and this is not a cache replay. Preserve the
    // original level/cache accounting rather than inventing new provenance.
    projected.summary.max_level = original.summary.max_level;
    projected.summary.cached = original.summary.cached;
    Some(projected)
}

#[cfg(test)]
mod tests;
