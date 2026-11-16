//! Accept bounded source work on the SAME actual source/graph. No completion
//! or configuration successor is issued from acceptance DATA.
use trust_resource_controller::bootstrap_graph::offline_preparation::{
    ArchiveCandidate, SourceCaptureAccepted,
};

use super::*;

struct Retained<'a> {
    source: &'a OriginalPreparationSource,
    returned: bool,
}
impl Drop for Retained<'_> {
    fn drop(&mut self) {
        if !self.returned {
            self.source.quarantine();
        }
    }
}
impl OriginalPreparationSource {
    /// Candidate names/digests are bounded DATA only. The client obtains the
    /// entire original114 from its retained actual137 state, never these rows.
    /// This one-use acceptance leaves actual source/output/cache/scope owners
    /// retained on the SAME graph; Config remains refused pending real closure.
    pub fn capture_preparation_source(
        &self,
        candidates: Vec<ArchiveCandidate>,
    ) -> io::Result<SourceCaptureAccepted> {
        let mut held = Retained { source: self, returned: false };
        let result = (|| {
            let candidates = Arc::new(candidates);
            {
                let mut retained = lock(&self.original.source_capture, self.original.end)?;
                if retained.is_some() {
                    return Err(io::Error::other("original source capture is one-use"));
                }
                *retained = Some(Arc::clone(&candidates)); // BEFORE validation, preflight or send
            }
            self.graph.capture_preparation_source(&self.original, candidates)
        })();
        held.returned = result.is_ok();
        self.record(result)
    }
}
impl OriginalHostGraph {
    fn capture_preparation_source(
        &self,
        source: &Arc<SourceStage>,
        candidates: Arc<Vec<ArchiveCandidate>>,
    ) -> io::Result<SourceCaptureAccepted> {
        let result = (|| {
            self.check()?;
            source.check_current()?;
            if !matches!(&source.selection, SourceSelection::Staged(_))
                || !source.programs_finalized.load(Ordering::Acquire)
                || !lock(&source.caller_cache, source.end)?.bound
            {
                return Err(io::Error::other(
                    "source capture requires actual staged programs/cache custody",
                ));
            }
            // Bound the only clone below through the maintained shared path
            // predicate; the canonical138 codec still owns complete validation.
            if candidates.len() > trust_resource_controller::bootstrap_graph::offline_preparation::MAX_ARCHIVE_CANDIDATES
                || candidates.iter().any(|candidate| !configuration::relative(&candidate.relative))
            {
                return Err(io::Error::other("source capture candidate allocation bound exceeded"));
            }
            let mut scheduler = lock(&super::super::super::super::selected()?.state, source.end)?;
            if scheduler.producer_failed || !scheduler.embedded_original {
                return Err(io::Error::other("source capture requires its original scheduler"));
            }
            let mut state = lock(&self.state, source.end)?;
            if state.failed
                || state.source_task_active
                || state.preparation_inputs.is_some()
                || state.preparation_source.as_ref().is_none_or(|same| !Arc::ptr_eq(same, source))
                || state
                    .dependency_owners
                    .as_ref()
                    .is_none_or(|same| !Arc::ptr_eq(same, &source.owners))
                || lock(&source.source_capture, source.end)?
                    .as_ref()
                    .is_none_or(|same| !Arc::ptr_eq(same, &candidates))
            {
                return Err(io::Error::other(
                    "source capture lost its SAME original owner/attempt",
                ));
            }
            let end = source.end.min(state.input_deadline).min(self.deadline);
            state.failed = true;
            scheduler.producer_failed = true;
            let (delivered, retained_end) = {
                let State { source_offer, phase, .. } = &mut *state;
                let Some(Phase::SourceBound(bound)) = phase else {
                    return Err(io::Error::other(
                        "source capture requires its SAME source channel",
                    ));
                };
                let delivered = source_offer
                    .as_ref()
                    .ok_or_else(|| io::Error::other("original source offer is absent"))?
                    .with_descriptions(|files, _| {
                        // SAFETY: SAME graph-retained source/output/cache/scope
                        // owners; real SourceOffer bookends these four borrowed
                        // descriptions through success, refusal and unwind.
                        Ok(unsafe {
                            bound.capture_original_preparation_source(
                                candidates.as_ref().clone(),
                                &files,
                                end,
                            )
                        })
                    });
                (delivered, bound.original_deadline())
            };
            state.input_deadline = state.input_deadline.min(retained_end).min(end);
            let accepted = delivered??;
            source.check_current()?;
            scope_current(&state)?;
            time(state.input_deadline)?;
            //139 accepted pending work only. Keep the attempt in SourceStage;
            // configuration_ready and the client BOTH refuse Config after it.
            state.failed = false;
            scheduler.producer_failed = false;
            Ok(accepted)
        })();
        if result.is_err() {
            self.fail_preparation();
        }
        result
    }
}
