//! Current-body publication preparation. This holds owned presentation DATA
//! only until the caller seals it, never a full verification/native carrier.
//! Source/private effects stay in the sole original publisher and run once.

use super::*;
use super::super::publication_human::HumanFacts;
use super::super::publication_transport::{
    PreparedTransportData, prepare_transport_json_with_modeled_facts,
};

pub(super) struct HumanPreparation {
    pub(super) action: usize,
    pub(super) span: rustc_span::Span,
    pub(super) facts: HumanFacts,
    pub(super) original_tally: PublishedRowTally,
}

pub(super) struct PreparedTransport {
    pub(super) action: usize,
    pub(super) span: rustc_span::Span,
    pub(super) data: PreparedTransportData,
}

pub(super) struct PreparedCollection {
    pub(super) actions: Vec<PreparedAction>,
    // Transport occurs at its ORIGINAL position in the action stream, before
    // policy diagnostics. The live span is not serialized by this wrapper.
    pub(super) transport: Option<PreparedTransport>,
    pub(super) human: Option<HumanPreparation>,
    pub(super) owed: Option<publication_identity::OwedInventory>,
}

impl PreparedCollection {
    fn new() -> Self {
        Self { actions: Vec::new(), transport: None, human: None, owed: None }
    }

    /// An admission/write failure uses these SAME prepared original facts.
    /// No source/helper/validator/ledger call is repeated to obtain fallback.
    pub(super) fn emit_original(self, tcx: TyCtxt<'_>) {
        self.emit(tcx, None);
    }

    /// Only the fresh token consumer can supply the already fitted selected
    /// transport. Original eager semantic/caller/ledger facts are never rerun.
    pub(super) fn emit_selected(
        self,
        tcx: TyCtxt<'_>,
        selected: super::super::publication_transport::FittedFunctionTransport,
    ) {
        self.emit(tcx, Some(selected));
    }

    fn emit(
        self,
        tcx: TyCtxt<'_>,
        mut selected: Option<super::super::publication_transport::FittedFunctionTransport>,
    ) {
        let Self { actions, mut transport, human: _, owed: _ } = self;
        let mut immediate = ImmediatePublication;
        for (index, action) in actions.into_iter().enumerate() {
            if transport.as_ref().is_some_and(|transport| transport.action == index) {
                let live = transport.take().expect("same original transport position");
                if let Some(selected) = selected.take() {
                    selected.emit(tcx, live.span);
                } else {
                    live.data.emit(tcx, live.span);
                }
            }
            immediate.action(tcx, action);
        }
        if let Some(live) = transport {
            if let Some(selected) = selected.take() {
                selected.emit(tcx, live.span);
            } else {
                live.data.emit(tcx, live.span);
            }
        }
        if selected.is_some() {
            tcx.dcx().err("Trust selected publication has no original transport position; report refused");
        }
    }
}

/// `None` means admission failed and all original output was already flushed.
/// The owner MUST NOT rerun the original publisher in that case. It may keep
/// running its remaining source work with immediate output through this sink.
pub(super) struct CollectedPublication<'clock> {
    prepared: Option<PreparedCollection>,
    clock: Option<&'clock PendingClock>,
}

fn preparation_allows(clock: Option<&PendingClock>) -> bool {
    trust_certify::calculus_row::base::preparation_stop().is_none()
        && match clock {
            Some(clock) => clock.deadline().is_ok_and(report_deadline_allows),
            // No actual native computation means ORIGINAL-only output. It
            // must not be given a fabricated function deadline/credit mark.
            None => report_deadline_allows(trust_types::verify_budget::current_deadline()),
        }
}

impl<'clock> CollectedPublication<'clock> {
    pub(super) fn new(clock: Option<&'clock PendingClock>) -> Self {
        Self { prepared: Some(PreparedCollection::new()), clock }
    }

    pub(super) fn finish(self) -> Option<PreparedCollection> { self.prepared }

    fn flush_original(&mut self, tcx: TyCtxt<'_>) {
        if let Some(prepared) = self.prepared.take() {
            prepared.emit_original(tcx);
        }
    }
}

fn original_aborting_action(action: &PreparedAction) -> bool {
    match action {
        PreparedAction::Diagnostic(diagnostic) | PreparedAction::LevelZeroRowFailure(diagnostic) => {
            diagnostic.diagnostic.aborting
        }
        PreparedAction::FullFailure { failure, .. } => failure.diagnostic().aborting,
        PreparedAction::Note(_) | PreparedAction::Stderr(_) => false,
    }
}

impl PublicationOutput for CollectedPublication<'_> {
    fn original_rows(
        &mut self,
        tcx: TyCtxt<'_>,
        rows: &[TransportObligationResult],
        tally: PublishedRowTally,
    ) {
        if !preparation_allows(self.clock) {
            self.flush_original(tcx);
            return;
        }
        let clock = self.clock;
        let Some(prepared) = self.prepared.as_mut() else { return };
        if prepared.owed.is_some() {
            self.flush_original(tcx);
            return;
        }
        match publication_identity::OwedInventory::capture(rows, tally, || preparation_allows(clock)) {
            Ok(owed) => prepared.owed = Some(owed),
            Err(error) => {
                debug!("VF5 original inventory admission refused: {error}; ordinary output remains");
                self.flush_original(tcx);
            }
        }
    }

    fn action(&mut self, tcx: TyCtxt<'_>, action: PreparedAction) {
        if !preparation_allows(self.clock) { self.flush_original(tcx); }
        if let Some(prepared) = self.prepared.as_mut() {
            if prepared.actions.try_reserve(1).is_ok() {
                if original_aborting_action(&action) {
                    publication_errors::record_original_abort(tcx.sess);
                }
                prepared.actions.push(action);
                return;
            }
            // The current action remains owned here. Flush the prefix and it
            // in the original order, then keep ordinary immediate behavior.
            self.flush_original(tcx);
        }
        ImmediatePublication.action(tcx, action);
    }

    fn original_errors_unchanged(&self, tcx: TyCtxt<'_>, baseline: &OriginalErrorBaseline) -> bool {
        publication_errors::unchanged(tcx, baseline)
    }

    fn results_report(
        &mut self,
        tcx: TyCtxt<'_>,
        span: rustc_span::Span,
        results: &[(VerificationCondition, VerificationResult)],
        bindings: &[Option<ResultObligationBinding>],
        authorities: &[Option<ResultProofAuthority>],
        certified: usize,
        published_rows: PublishedRowTally,
        conditional_on_coroutine_premise: bool,
    ) {
        if !preparation_allows(self.clock) { self.flush_original(tcx); }
        let Some(facts) = super::super::publication_human::capture(
            tcx.sess, results, bindings, authorities, certified,
            conditional_on_coroutine_premise,
        ) else { return };
        let Some(report) = facts.render(published_rows, &[]) else {
            // Empty proposed inventory must always reproduce original facts.
            // A protocol defect cannot silently remove a function's report.
            self.flush_original(tcx);
            tcx.dcx().err("Trust could not render its original prepared verification report");
            return;
        };
        let action_index = self.prepared.as_ref().map(|prepared| prepared.actions.len());
        let duplicate = self.prepared.as_ref().is_some_and(|prepared| prepared.human.is_some());
        if duplicate { self.flush_original(tcx); }
        self.action(tcx, PreparedAction::Note(PreparedLocatedNote { span, report }));
        if !duplicate
            && let (Some(prepared), Some(action)) = (self.prepared.as_mut(), action_index)
        {
            prepared.human = Some(HumanPreparation {
                action, span, facts, original_tally: published_rows,
            });
        }
    }

    fn transport(
        &mut self,
        tcx: TyCtxt<'_>,
        def_id: Option<LocalDefId>,
        func_path: &str,
        rows: &[TransportObligationResult],
        cached: u32,
        modeled_facts: &[String],
        expanded_function_identity: Option<
            &trust_types::expanded_function_identity::ExpandedFunctionIdentity,
        >,
    ) {
        if !preparation_allows(self.clock) { self.flush_original(tcx); }
        if self.prepared.as_ref().is_some_and(|prepared| prepared.transport.is_some()) {
            self.flush_original(tcx);
        }
        if self.prepared.is_none() {
            ImmediatePublication.transport(
                tcx, def_id, func_path, rows, cached, modeled_facts, expanded_function_identity,
            );
            return;
        }
        // Original materialization/source/identity work runs once NOW. The
        // final data emitter has no source/private-proof queries to repeat.
        let transport = prepare_transport_json_with_modeled_facts(
            tcx, def_id, func_path, rows, cached, modeled_facts, expanded_function_identity,
        );
        let (span, data) = transport.split();
        // The original transport prefix may append its existing explicit
        // argument-premise row. The owed inventory includes that ACTUAL row,
        // not only the earlier human-policy slice or the VC denominator.
        let original_rows = &data.result().results;
        let owed = match publication_identity::OwedInventory::capture(
            original_rows, PublishedRowTally::of(original_rows, None),
            || preparation_allows(self.clock),
        ) {
            Ok(owed) => owed,
            Err(error) => {
                debug!("VF5 final original inventory refused: {error}; ordinary output remains");
                self.flush_original(tcx);
                data.emit(tcx, span);
                return;
            }
        };
        let prepared = self.prepared.as_mut().expect("no source callback owns this stack sink");
        prepared.owed = Some(owed);
        prepared.transport = Some(PreparedTransport { action: prepared.actions.len(), span, data });
    }
}
