//! Same original staged source -> physical caller directory. This retains the
//! descriptor-accounted producer; only the native State acquires the cache lock.
use trust_resource_controller::bootstrap_graph::offline_preparation::Request;
use trust_resource_controller::descriptors::AdmittedDirectory;

use super::*;

pub(super) struct Inputs {
    pub(super) directory: Option<Arc<AdmittedDirectory>>,
    pub(super) bound: bool,
}
impl Inputs {
    pub(super) fn new(complete126: bool) -> Self {
        Self { directory: None, bound: complete126 }
    }
}

impl OriginalPreparationSource {
    /// The actual original full environment, before Config. This is private
    /// command DATA for the runtime context equality check, never a cache or
    /// configuration issuer. Do not print its values.
    pub fn preparation_environment(&self) -> io::Result<&[(Vec<u8>, Vec<u8>)]> {
        self.check_current()?;
        self.record(if self.original.programs_finalized.load(Ordering::Acquire) {
            Ok(self.original.selection.environment())
        } else {
            Err(io::Error::other("caller cache requires finalized original programs"))
        })
    }

    /// Consume the actual context-side capture result. Even capture refusal
    /// permanently quarantines this SAME source/graph. Accepted137 is DATA;
    /// it cannot return a cache lock, native closure, Seed or SDK owner.
    ///
    /// # Safety
    /// On Ok, the runtime must have selected this directory with the original
    /// Targo GlobalContext, checked its complete original cwd/environment and
    /// untouched Config state, and captured the SAME actual readonly original
    /// through the maintained descriptor budget. A pathname, reconstructed
    /// file, arbitrary observer or DTO cannot establish that association.
    /// `runtime_current` is a negative context veto only and must not reenter
    /// the locked Source/Graph; successful observer DATA creates no owner.
    pub unsafe fn attach_original_preparation_cache(
        &self,
        captured: io::Result<Arc<AdmittedDirectory>>,
        runtime_current: impl FnMut() -> io::Result<()>,
    ) -> io::Result<Request> {
        let result = (|| {
            let directory = captured?;
            {
                let mut retained = lock(&self.original.caller_cache, self.original.end)?;
                if retained.directory.is_some() || retained.bound {
                    return Err(io::Error::other("original caller-cache handoff is one-use"));
                }
                retained.directory = Some(Arc::clone(&directory)); // BEFORE all preflight and wire IO
            }
            self.graph.attach_preparation_caller_cache(&self.original, directory, runtime_current)
        })();
        self.record(result)
    }
}

impl OriginalHostGraph {
    fn attach_preparation_caller_cache(
        &self,
        source: &Arc<SourceStage>,
        directory: Arc<AdmittedDirectory>,
        mut runtime_current: impl FnMut() -> io::Result<()>,
    ) -> io::Result<Request> {
        let result = (|| {
            self.check()?;
            source.check_current()?;
            if !matches!(&source.selection, SourceSelection::Staged(_))
                || !source.programs_finalized.load(Ordering::Acquire)
            {
                return Err(io::Error::other(
                    "caller cache requires its actual staged program selection",
                ));
            }
            let mut scheduler = lock(&super::super::super::super::selected()?.state, source.end)?;
            if scheduler.producer_failed || !scheduler.embedded_original {
                return Err(io::Error::other("caller cache requires its original scheduler"));
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
            {
                return Err(io::Error::other(
                    "caller cache cannot replace original source/input owners",
                ));
            }
            {
                let retained = lock(&source.caller_cache, source.end)?;
                if retained.bound
                    || retained.directory.as_ref().is_none_or(|same| !Arc::ptr_eq(same, &directory))
                {
                    return Err(io::Error::other("caller cache lost its SAME physical producer"));
                }
            }
            let end = source.end.min(state.input_deadline).min(self.deadline);
            state.failed = true;
            scheduler.producer_failed = true;
            let (delivered, retained_end) = {
                let State { source_offer, phase, .. } = &mut *state;
                let Some(Phase::SourceBound(bound)) = phase else {
                    return Err(io::Error::other(
                        "caller cache requires the same accepted Source channel",
                    ));
                };
                let delivered = source_offer
                    .as_ref()
                    .ok_or_else(|| io::Error::other("caller cache lost its original source offer"))?
                    .with_descriptions(|files, _| {
                        // SAFETY: actual runtime capture contract above; State
                        // retains exact SourceStage/OwnedInputs/physical Arc,
                        // and this callback bookends the SAME SourceOffer FDs.
                        Ok(unsafe {
                            bound.attach_original_preparation_cache(
                                Arc::clone(&directory),
                                &files,
                                end,
                                &mut runtime_current,
                            )
                        })
                    });
                (delivered, bound.original_deadline())
            };
            state.input_deadline = state.input_deadline.min(retained_end).min(end);
            let request = delivered??;
            source.check_current()?;
            directory.validate(state.input_deadline)?;
            scope_current(&state)?;
            time(state.input_deadline)?;
            lock(&source.caller_cache, state.input_deadline)?.bound = true;
            state.failed = false;
            scheduler.producer_failed = false;
            Ok(request)
        })();
        if result.is_err() {
            self.fail_preparation();
        }
        result
    }
}
