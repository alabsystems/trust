//! Actual Bootstrap configuration issuers under the SAME protected source.
//! This is distinct from Aterm's resident OriginalMaterializationInputs. Only
//! the authenticated original graph can join its Managers, accepted native
//! materialization and these original readonly producers. No DATA creates it.
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};

use build_helper::trust_repo_lock::management::WeakScopeDispatch;
use trust_resource_controller::bootstrap_graph::configuration;
use trust_resource_provenance::program::HeldSourceReadSet;

use super::*;

mod capture;
use capture::SelectedFile;

struct Captures {
    files: Vec<Arc<SelectedFile>>,
    bytes: u64,
}
pub(in crate::utils::metadata_scheduler::host_graph) struct Inputs {
    source: Arc<OriginalSourceRoot>,
    scope: WeakScopeDispatch,
    key: Key,
    selection: trust_resource_controller::bootstrap_graph::offline_preparation::IntentSelection,
    creator: u32,
    end: Mutex<Instant>,
    captures: Mutex<Captures>,
    selected_root: Mutex<Option<HeldSourceReadSet>>,
    busy: AtomicBool,
    parsing: AtomicBool,
    failed: AtomicBool,
    finished: AtomicBool,
}
impl Inputs {
    fn new(
        source: Arc<OriginalSourceRoot>,
        scope: WeakScopeDispatch,
        key: Key,
        selection: trust_resource_controller::bootstrap_graph::offline_preparation::IntentSelection,
        end: Instant,
    ) -> Self {
        Self {
            source,
            scope,
            key,
            selection,
            creator: std::process::id(),
            end: Mutex::new(end),
            captures: Mutex::new(Captures { files: Vec::new(), bytes: 0 }),
            selected_root: Mutex::new(None),
            busy: AtomicBool::new(false),
            parsing: AtomicBool::new(false),
            failed: AtomicBool::new(false),
            finished: AtomicBool::new(false),
        }
    }
    fn deadline(&self) -> io::Result<Instant> {
        Ok(*lock(&self.end, self.source.deadline())?)
    }
    fn restrict(&self, end: Instant) -> io::Result<()> {
        let result = (|| {
            let mut original = lock(&self.end, self.source.deadline())?;
            *original = (*original).min(end);
            time(*original)
        })();
        self.record(result)
    }
    fn quarantine(&self) {
        self.failed.store(true, Ordering::Release);
        if let Ok(scope) = self.scope.upgrade() {
            scope.record_failure("original preparation configuration refused");
        }
    }
    fn capture_root(&self) -> io::Result<()> {
        let result = (|| {
            let end = self.deadline()?;
            self.source.check_current()?;
            let mut selected = lock(&self.selected_root, end)?;
            if selected.is_some() {
                return Err(io::Error::other("configuration root capture is one-use"));
            }
            *selected = Some(HeldSourceReadSet::capture(self.source.directory()?, end)?);
            self.source.check_current()?;
            time(end)
        })();
        self.record(result)
    }
    fn record<T>(&self, result: io::Result<T>) -> io::Result<T> {
        if result.is_err() {
            self.quarantine();
        }
        result
    }
    pub(in crate::utils::metadata_scheduler::host_graph) fn check_current(&self) -> io::Result<()> {
        let result = (|| {
            let end = self.deadline()?;
            time(end)?;
            if self.creator != std::process::id() || self.failed.load(Ordering::Acquire) {
                return Err(io::Error::other(
                    "original preparation inputs are foreign or quarantined",
                ));
            }
            self.source.check_current()?;
            lock(&self.selected_root, end)?
                .as_ref()
                .ok_or_else(|| io::Error::other("original configuration root capture is absent"))?
                .check_current(self.source.directory()?)?;
            time(end)?;
            let captures = lock(&self.captures, end)?;
            for file in &captures.files {
                time(end)?;
                file.check_current(end)?;
            }
            self.source.check_current()?;
            time(end)
        })();
        self.record(result)
    }
    fn begin_read(self: &Arc<Self>) -> io::Result<ReadEpoch> {
        self.check_current()?;
        if self.finished.load(Ordering::Acquire)
            || self.busy.compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire).is_err()
        {
            return self
                .record(Err(io::Error::other("original configuration reader is sealed or busy")));
        }
        Ok(ReadEpoch { original: Arc::clone(self), complete: false })
    }
    fn relative(&self, path: &Path) -> io::Result<Vec<u8>> {
        let relative = if path.is_absolute() {
            path.strip_prefix(self.source.path()).map_err(io::Error::other)?
        } else {
            path
        };
        let relative = relative.as_os_str().as_bytes();
        if !configuration::relative(relative) {
            return Err(io::Error::other(
                "configuration is not an original source-relative selector",
            ));
        }
        Ok(relative.to_vec())
    }
    fn cached(&self, path: &Path) -> io::Result<Arc<SelectedFile>> {
        let result = (|| {
            self.check_current()?;
            let relative = self.relative(path)?;
            lock(&self.captures, self.deadline()?)?
                .files
                .iter()
                .find(|file| file.relative() == relative.as_slice())
                .cloned()
                .ok_or_else(|| {
                    io::Error::other("late source input has no original captured producer")
                })
        })();
        self.record(result)
    }
    fn read(&self, path: &Path) -> io::Result<Arc<SelectedFile>> {
        let result = (|| {
            self.check_current()?;
            let end = self.deadline()?;
            let relative = self.relative(path)?;
            let mut captures = lock(&self.captures, end)?;
            if let Some(file) =
                captures.files.iter().find(|file| file.relative() == relative.as_slice())
            {
                return Ok(Arc::clone(file));
            }
            if captures.files.len() >= configuration::MAX_FILES
                || captures.bytes >= configuration::MAX_BYTES
            {
                return Err(io::Error::other("complete configuration file bound exceeded"));
            }
            let file = Arc::new(SelectedFile::pending(Arc::clone(&self.source), relative, end));
            captures.files.push(Arc::clone(&file)); // partial producer retained BEFORE opening/reading
            let sequence = captures.files.len() as u64;
            file.capture(&self.key, sequence, |bytes| {
                let total = captures
                    .bytes
                    .checked_add(bytes)
                    .ok_or_else(|| io::Error::other("configuration byte count overflow"))?;
                if total > configuration::MAX_BYTES {
                    return Err(io::Error::other("complete configuration byte bound exceeded"));
                }
                captures.bytes = total; // no refund on any later refusal
                Ok(())
            })?;
            drop(captures);
            self.check_current()?;
            Ok(file)
        })();
        self.record(result)
    }
    fn all_offered(&self) -> io::Result<()> {
        self.check_current()?;
        if self.busy.load(Ordering::Acquire) {
            return Err(io::Error::other("original configuration callback is still active"));
        }
        let end = self.deadline()?;
        for file in &lock(&self.captures, end)?.files {
            if !file.offered(end)? {
                return Err(io::Error::other("original configuration offer remains unresolved"));
            }
        }
        Ok(())
    }
    fn with_parser<T, E>(
        self: &Arc<Self>,
        contents: &str,
        parse: &mut impl FnMut(&str) -> Result<T, E>,
    ) -> io::Result<Result<T, E>> {
        let epoch = self.begin_read()?;
        match catch_unwind(AssertUnwindSafe(|| parse(contents))) {
            Ok(Ok(value)) => {
                epoch.finish()?;
                Ok(Ok(value))
            }
            Ok(Err(error)) => {
                self.quarantine();
                Ok(Err(error)) // preserve the actual parser's semantic error
            }
            Err(payload) => {
                self.quarantine();
                resume_unwind(payload)
            }
        }
    }
}
struct ReadEpoch {
    original: Arc<Inputs>,
    complete: bool,
}
impl ReadEpoch {
    fn finish(mut self) -> io::Result<()> {
        self.original.check_current()?;
        self.original.busy.store(false, Ordering::Release);
        self.complete = true;
        Ok(())
    }
}
impl Drop for ReadEpoch {
    fn drop(&mut self) {
        if !self.complete {
            self.original.quarantine();
        }
    }
}

/// Actual original Root/source/configuration custody. There is no constructor
/// from a path, accepted reply, rows or a SourceRoot alone. Drop quarantines the
/// SAME graph/resources; only a future genuine native close plus local joins
/// may dispose them. This is not a Seed, SDK or readiness result.
pub struct OriginalPreparationInputs {
    graph: ManuallyDrop<Arc<OriginalHostGraph>>,
    original: Arc<Inputs>,
}
impl OriginalPreparationInputs {
    pub fn original_deadline(&self) -> io::Result<Instant> {
        self.original.deadline()
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.graph.check()?;
        self.original.all_offered()
    }
}
impl Drop for OriginalPreparationInputs {
    fn drop(&mut self) {
        self.original.quarantine();
    }
}

/// Physical guards for the actual before-Config source stage. The graph retains
/// this SAME value so another graph alias cannot bypass its read-set checks.
/// No constructor accepts paths, observations or caller-authored owner rows.
pub(in crate::utils::metadata_scheduler::host_graph) struct SourceStage {
    owners: Arc<OwnedInputs>,
    selection: trust_resource_controller::bootstrap_graph::offline_preparation::IntentSelection,
    creator: u32,
    end: Instant,
    selected: Mutex<Option<HeldSourceReadSet>>,
    failed: AtomicBool,
}
impl SourceStage {
    fn new(
        owners: Arc<OwnedInputs>,
        selection: trust_resource_controller::bootstrap_graph::offline_preparation::IntentSelection,
        end: Instant,
    ) -> Self {
        Self {
            end: end.min(owners.deadline),
            owners,
            selection,
            creator: std::process::id(),
            selected: Mutex::new(None),
            failed: AtomicBool::new(false),
        }
    }
    fn quarantine(&self) {
        self.failed.store(true, Ordering::Release);
        if let Ok(scope) = lock(&self.owners.scope, self.owners.deadline) {
            if let Some(scope) = scope.as_ref() {
                scope.dispatcher().record_failure("original preparation source refused");
            }
        }
    }
    fn record<T>(&self, result: io::Result<T>) -> io::Result<T> {
        if result.is_err() {
            self.quarantine();
        }
        result
    }
    fn source(&self) -> io::Result<&OriginalSourceRoot> {
        self.owners
            .source
            .get()
            .map(Arc::as_ref)
            .ok_or_else(|| io::Error::other("actual preparation source is absent"))
    }
    fn capture_root(&self) -> io::Result<()> {
        let result = (|| {
            self.owners.check()?;
            time(self.end)?;
            let source = self.source()?;
            let mut selected = lock(&self.selected, self.end)?;
            if selected.is_some() {
                return Err(io::Error::other("original source root capture is one-use"));
            }
            *selected = Some(HeldSourceReadSet::capture(source.directory()?, self.end)?);
            drop(selected);
            self.check_current()
        })();
        self.record(result)
    }
    pub(in crate::utils::metadata_scheduler::host_graph) fn check_current(&self) -> io::Result<()> {
        let result = (|| {
            time(self.end)?;
            if self.creator != std::process::id() || self.failed.load(Ordering::Acquire) {
                return Err(io::Error::other(
                    "original preparation source is foreign or quarantined",
                ));
            }
            self.owners.check()?;
            lock(&self.selected, self.end)?
                .as_ref()
                .ok_or_else(|| io::Error::other("actual preparation root capture is absent"))?
                .check_current(self.source()?.directory()?)?;
            self.owners.check()?;
            time(self.end)
        })();
        self.record(result)
    }
}

/// Actual original source/output Managers and accepted native materialization,
/// before Bootstrap Config. The native phase remains SourceBound and unsealed;
/// neither its contents identity nor this owner selects a private tool pathname.
/// Drop quarantines the SAME graph and retains its actual resources.
pub struct OriginalPreparationSource {
    graph: ManuallyDrop<Arc<OriginalHostGraph>>,
    original: Arc<SourceStage>,
    transferred: bool,
}
impl OriginalPreparationSource {
    fn record<T>(&self, result: io::Result<T>) -> io::Result<T> {
        if result.is_err() {
            self.graph.fail_preparation();
        }
        result
    }
    pub fn original_deadline(&self) -> io::Result<Instant> {
        self.record(self.graph.input_deadline().map(|end| end.min(self.original.end)))
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.record(self.graph.check().and_then(|()| self.original.check_current()))
    }
    pub fn original_source(&self) -> io::Result<&OriginalSourceRoot> {
        self.check_current()?;
        self.record(self.original.source())
    }
    /// Accepted observation only: this does not grant namespace/Seed authority.
    pub fn materialization_contents(&self) -> io::Result<FileIdentity> {
        let result = (|| {
            self.check_current()?;
            let state = lock(&self.graph.state, self.original.end)?;
            match &state.phase {
                Some(Phase::SourceBound(bound)) => bound
                    .materialization_contents()
                    .ok_or_else(|| io::Error::other("actual materialization contents are absent")),
                _ => Err(io::Error::other("original preparation source phase changed")),
            }
        })();
        self.record(result)
    }
    /// Explicitly consume this SAME source stage to enable the existing Config
    /// callbacks. The closed source/output route need not parse Bootstrap Config.
    pub fn begin_configuration(mut self) -> io::Result<OriginalPreparationInputs> {
        let result = self.graph.activate_preparation_configuration(&self.original);
        match result {
            Ok(original) => {
                self.transferred = true;
                // The successor and State already retain the same actual graph.
                unsafe { ManuallyDrop::drop(&mut self.graph) };
                Ok(original)
            }
            Err(error) => Err(error), // Drop quarantines and retains the same graph.
        }
    }
}
impl Drop for OriginalPreparationSource {
    fn drop(&mut self) {
        if !self.transferred {
            self.graph.fail_preparation();
        }
    }
}

impl OriginalHostGraph {
    /// Begin only on the original support's authenticated retained intent.
    /// Acquire the existing Managers and accept native materialization without
    /// invoking Bootstrap Config or claiming configuration/output completion.
    pub fn begin_closed_offline_preparation_source(
        self: &Arc<Self>,
    ) -> io::Result<OriginalPreparationSource> {
        let result = (|| {
            self.check()?;
            let intent = {
                let state = lock(&self.state, self.deadline)?;
                let Some(Phase::Supported(support)) = &state.phase else {
                    return Err(io::Error::other(
                        "offline preparation needs its original supported Root",
                    ));
                };
                support
                    .offline_preparation_intent(self.deadline)?
                    .cloned()
                    .ok_or_else(|| io::Error::other("original offline intent is absent"))?
            };
            self.prepare_dependency_entry()?;
            let source = PathBuf::from(OsString::from(std::ffi::OsStr::from_bytes(
                &intent.selection.source_root,
            )));
            let output = PathBuf::from(OsString::from(std::ffi::OsStr::from_bytes(
                &intent.selection.output_root,
            )));
            if std::env::current_dir()?.as_os_str() != source.as_os_str() {
                return Err(io::Error::other("offline preparation left its original source cwd"));
            }
            let owners = Arc::new(OwnedInputs::acquire(&source, &output, self.deadline)?);
            {
                let mut state = lock(&self.state, self.deadline)?;
                if state.dependency_owners.is_some()
                    || state.preparation_source.is_some()
                    || state.preparation_inputs.is_some()
                {
                    return Err(io::Error::other("original preparation owner is one-use"));
                }
                state.dependency_owners = Some(Arc::clone(&owners));
            }
            owners.protect(&source)?;
            let dispatch = lock(&owners.scope, self.deadline)?
                .as_ref()
                .ok_or_else(|| io::Error::other("actual preparation scope is absent"))?
                .dispatcher();
            self.enroll_original_source(
                dispatch.downgrade(),
                Arc::clone(owners.source.get().unwrap()),
                &source,
                &output,
            )
            .map_err(io::Error::other)?;
            let mut scheduler = lock(&super::super::super::selected()?.state, self.deadline)?;
            if scheduler.producer_failed || !scheduler.embedded_original {
                return Err(io::Error::other("materialization requires the original scheduler"));
            }
            let mut state = lock(&self.state, self.deadline)?;
            if state.failed || state.source_task_active {
                return Err(io::Error::other("original preparation is unresolved"));
            }
            state.failed = true;
            scheduler.producer_failed = true;
            let Some(Phase::SourceBound(original)) = state.phase.take() else {
                return Err(io::Error::other(
                    "native materialization needs its same original source",
                ));
            };
            let prepared = state
                .source_offer
                .as_ref()
                .ok_or_else(|| io::Error::other("actual source offer is absent"))?
                .with_descriptions(|files, _| {
                    // SAFETY: State retains the actual same-scope SourceOffer and
                    // its callback bookends the complete exchange including error.
                    Ok(unsafe { (*original).prepare_materialization(&files, self.deadline) })
                })?;
            let prepared = match prepared {
                Ok(original) => original,
                Err(error) => {
                    state.graph_failure = Some(error);
                    return Err(io::Error::other(
                        "native preparation refused; original custody retained",
                    ));
                }
            };
            let end = prepared.original_deadline().min(state.input_deadline).min(self.deadline);
            // Retain the opaque returned phase BEFORE any fallible postcheck.
            // A missing observation is never permission to dispose native custody.
            state.phase = Some(Phase::SourceBound(Box::new(prepared)));
            state.input_deadline = end;
            let Some(Phase::SourceBound(prepared)) = &state.phase else { unreachable!() };
            if prepared.materialization().is_none() || prepared.materialization_contents().is_none()
            {
                return Err(io::Error::other("accepted native materialization is missing"));
            }
            let original = Arc::new(SourceStage::new(owners, intent.selection, end));
            state.preparation_source = Some(Arc::clone(&original));
            original.capture_root()?;
            scope_current(&state)?;
            time(state.input_deadline)?;
            state.failed = false;
            scheduler.producer_failed = false;
            Ok(OriginalPreparationSource {
                graph: ManuallyDrop::new(Arc::clone(self)),
                original,
                transferred: false,
            })
        })();
        result.map_err(|error| {
            self.fail_preparation();
            io::Error::new(
                error.kind(),
                Refused { error, graph: ManuallyDrop::new(Arc::clone(self)) },
            )
        })
    }

    /// The existing Config issuer is explicitly downstream of the SAME source
    /// stage; neither route duplicates source acquisition or materialization.
    pub fn begin_offline_preparation_inputs(
        self: &Arc<Self>,
    ) -> io::Result<OriginalPreparationInputs> {
        self.begin_closed_offline_preparation_source()?.begin_configuration()
    }

    fn activate_preparation_configuration(
        self: &Arc<Self>,
        source: &Arc<SourceStage>,
    ) -> io::Result<OriginalPreparationInputs> {
        let result = (|| {
            self.check()?;
            source.check_current()?;
            let mut scheduler = lock(&super::super::super::selected()?.state, source.end)?;
            if scheduler.producer_failed || !scheduler.embedded_original {
                return Err(io::Error::other("configuration needs the original scheduler"));
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
                || !matches!(state.phase, Some(Phase::SourceBound(_)))
            {
                return Err(io::Error::other(
                    "configuration cannot replace its original source stage",
                ));
            }
            state.failed = true;
            scheduler.producer_failed = true;
            let dispatch = lock(&source.owners.scope, source.end)?
                .as_ref()
                .ok_or_else(|| io::Error::other("actual preparation scope is absent"))?
                .dispatcher();
            let original =
                Arc::new(Inputs::new(
                    Arc::clone(
                        source.owners.source.get().ok_or_else(|| {
                            io::Error::other("actual preparation source is absent")
                        })?,
                    ),
                    dispatch.downgrade(),
                    self.key.clone(),
                    source.selection.clone(),
                    source.end.min(state.input_deadline),
                ));
            state.preparation_inputs = Some(Arc::clone(&original));
            original.capture_root()?;
            scope_current(&state)?;
            time(state.input_deadline)?;
            state.failed = false;
            scheduler.producer_failed = false;
            Ok(OriginalPreparationInputs { graph: ManuallyDrop::new(Arc::clone(self)), original })
        })();
        if result.is_err() {
            self.fail_preparation();
        }
        result
    }
    fn fail_preparation(&self) {
        let (inputs, source, scope) = if let Ok(mut state) = lock(&self.state, self.deadline) {
            state.failed = true;
            (
                state.preparation_inputs.as_ref().cloned(),
                state.preparation_source.as_ref().cloned(),
                state.scope.as_ref().and_then(|scope| scope.upgrade().ok()),
            )
        } else {
            (None, None, None)
        };
        if let Some(source) = source {
            source.quarantine();
        }
        if let Some(inputs) = inputs {
            inputs.quarantine();
        }
        if let Some(scope) = scope {
            scope.record_failure("original preparation configuration refused");
        }
    }
    fn read_preparation_input(self: &Arc<Self>, path: &Path) -> io::Result<Option<String>> {
        let original = lock(&self.state, self.deadline)?.preparation_inputs.as_ref().cloned();
        let Some(original) = original else { return Ok(None) };
        let result = (|| {
            self.check()?;
            if std::env::current_dir()?.as_os_str() != original.source.path().as_os_str() {
                return Err(io::Error::other("original preparation cwd changed"));
            }
            if original.finished.load(Ordering::Acquire) {
                // No new offer/producer after the actual output seal. Reuse
                // only this SAME already retained source text under all guards.
                let selected = original.cached(path)?;
                let contents = selected.contents(original.deadline()?)?;
                original.check_current()?;
                self.check()?;
                return Ok(Some(contents));
            }
            if !original.parsing.load(Ordering::Acquire) {
                return Err(io::Error::other("original configuration parser is not active"));
            }
            let epoch = original.begin_read()?;
            let selected = original.read(path)?;
            let contents = selected.contents(original.deadline()?)?;
            if !selected.offered(original.deadline()?)? {
                let end = original.deadline()?;
                let offer = selected.offer(end)?;
                let mut scheduler = lock(&super::super::super::selected()?.state, end)?;
                if scheduler.producer_failed || !scheduler.embedded_original {
                    return Err(io::Error::other(
                        "configuration offer needs its original scheduler",
                    ));
                }
                let mut state = lock(&self.state, end)?;
                if state.failed
                    || state.source_task_active
                    || state
                        .preparation_inputs
                        .as_ref()
                        .is_none_or(|same| !Arc::ptr_eq(same, &original))
                    || state
                        .source
                        .as_ref()
                        .is_none_or(|source| !Arc::ptr_eq(source, &original.source))
                {
                    return Err(io::Error::other(
                        "configuration offer has another original source",
                    ));
                }
                scope_current(&state)?;
                state.failed = true;
                scheduler.producer_failed = true;
                let Some(Phase::SourceBound(bound)) = state.phase.take() else {
                    return Err(io::Error::other(
                        "configuration needs its materialized source phase",
                    ));
                };
                let offered = state
                    .source_offer
                    .as_ref()
                    .ok_or_else(|| io::Error::other("original source offer is absent"))?
                    .with_descriptions(|files, _| {
                        offer.check_current(end)?;
                        let description = offer.description(end)?;
                        // SAFETY: the retained producer is derived from the SAME
                        // OriginalSourceRoot after actual native materialization.
                        // Both it and the real SourceOffer bookend this exchange.
                        let result = unsafe {
                            (*bound).attach_original_configuration(
                                offer.request.clone(),
                                &files,
                                description,
                                end,
                            )
                        };
                        offer.check_current(end)?;
                        Ok(result)
                    })?;
                let bound = match offered {
                    Ok(bound) => bound,
                    Err(error) => {
                        state.graph_failure = Some(error);
                        return Err(io::Error::other(
                            "native configuration refused; original custody retained",
                        ));
                    }
                };
                let end = bound.original_deadline().min(end);
                state.phase = Some(Phase::SourceBound(Box::new(bound)));
                state.input_deadline = state.input_deadline.min(end);
                original.restrict(state.input_deadline)?;
                scope_current(&state)?;
                state.failed = false;
                scheduler.producer_failed = false;
                drop(state);
                drop(scheduler);
                selected.mark_offered(original.deadline()?)?;
            }
            original.check_current()?;
            self.check()?;
            epoch.finish()?;
            Ok(Some(contents))
        })();
        if result.is_err() {
            self.fail_preparation();
        }
        result
    }
    fn finish_preparation_configuration(self: &Arc<Self>, config: &Config) -> io::Result<()> {
        let (original, owners) = {
            let state = lock(&self.state, self.deadline)?;
            let Some(original) = &state.preparation_inputs else { return Ok(()) };
            let owners = state
                .dependency_owners
                .as_ref()
                .cloned()
                .ok_or_else(|| io::Error::other("actual preparation owners are absent"))?;
            (Arc::clone(original), owners)
        };
        let result = (|| {
            self.check()?;
            original.all_offered()?;
            if original.finished.load(Ordering::Acquire)
                || config.src.as_os_str() != original.source.path().as_os_str()
            {
                return Err(io::Error::other(
                    "configuration is sealed or selected another original source",
                ));
            }
            let output = {
                let state = lock(&self.state, self.deadline)?;
                let Some(Phase::SourceBound(bound)) = &state.phase else {
                    return Err(io::Error::other(
                        "configuration requires its source-bound original",
                    ));
                };
                PathBuf::from(std::ffi::OsStr::from_bytes(&bound.enrollment().output))
            };
            if config.out.as_os_str() != output.as_os_str() {
                return Err(io::Error::other("configuration selected another original output"));
            }
            if config.external_cargo.as_ref().is_none_or(|path| {
                path.as_os_str().as_bytes() != original.selection.configured_targo
            }) || config.external_rustc.as_ref().is_none_or(|path| {
                path.as_os_str().as_bytes() != original.selection.configured_compiler
            }) {
                return Err(io::Error::other(
                    "configuration retargeted the original configured tool spelling",
                ));
            }
            // SAFETY: the SAME actual OutputLock/command were acquired and
            // retained before enrollment; this exports only their originals.
            let descriptions = unsafe { owners.output.original_output(&owners.command, &output) }
                .map_err(io::Error::other)?;
            self.attach_output(
                &descriptions,
                Arc::clone(&owners.output),
                Arc::clone(&owners.command),
            )
            .map_err(io::Error::other)?;
            original.finished.store(true, Ordering::Release);
            original.check_current()?;
            self.check()
        })();
        if result.is_err() {
            self.fail_preparation();
        }
        result
    }
}
struct Refused {
    error: io::Error,
    #[allow(dead_code)]
    graph: ManuallyDrop<Arc<OriginalHostGraph>>,
}
impl std::fmt::Debug for Refused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefusedOriginalPreparationInputs")
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for Refused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for Refused {}

pub(crate) struct PreparationConfigParseGuard {
    graph: Arc<OriginalHostGraph>,
    original: Arc<Inputs>,
    complete: bool,
}
impl PreparationConfigParseGuard {
    pub(crate) fn finish(mut self, config: &Config) -> io::Result<()> {
        self.graph.finish_preparation_configuration(config)?;
        self.complete = true;
        Ok(())
    }
}
impl Drop for PreparationConfigParseGuard {
    fn drop(&mut self) {
        if !self.complete {
            self.original.quarantine();
            self.graph.fail_preparation();
        }
    }
}
pub(crate) fn begin_original_configuration_parse() -> io::Result<Option<PreparationConfigParseGuard>>
{
    let Some(original) = ORIGINAL.get() else { return Ok(None) };
    let graph = original
        .upgrade()
        .ok_or_else(|| io::Error::other("original native configuration owner expired"))?;
    let original = lock(&graph.state, graph.deadline)?.preparation_inputs.as_ref().cloned();
    let Some(original) = original else { return Ok(None) };
    graph.check()?;
    if original.finished.load(Ordering::Acquire)
        || original
            .parsing
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
    {
        graph.fail_preparation();
        return Err(io::Error::other("original configuration parser is sealed or already active"));
    }
    Ok(Some(PreparationConfigParseGuard { graph, original, complete: false }))
}
pub(crate) fn with_original_configuration<T, E>(
    path: &Path,
    parse: &mut impl FnMut(&str) -> Result<T, E>,
) -> io::Result<Option<Result<T, E>>> {
    let Some(original) = ORIGINAL.get() else { return Ok(None) };
    let original = original
        .upgrade()
        .ok_or_else(|| io::Error::other("original native configuration owner expired"))?;
    let Some(contents) = original.read_preparation_input(path)? else { return Ok(None) };
    let inputs = lock(&original.state, original.deadline)?
        .preparation_inputs
        .as_ref()
        .cloned()
        .ok_or_else(|| io::Error::other("original configuration issuer disappeared"))?;
    let result = inputs.with_parser(&contents, parse);
    match result {
        Ok(Ok(value)) => {
            original.check()?;
            Ok(Some(Ok(value)))
        }
        Ok(Err(error)) => {
            original.fail_preparation();
            Ok(Some(Err(error)))
        }
        Err(error) => {
            original.fail_preparation();
            Err(error)
        }
    }
}
pub(crate) fn check_original_configuration_path(path: &Path) -> io::Result<()> {
    let Some(original) = ORIGINAL.get() else { return Ok(()) };
    let original = original
        .upgrade()
        .ok_or_else(|| io::Error::other("original native configuration owner expired"))?;
    // Reuse the actual same capture/offer before the existing canonicalizer
    // could hide a literal link/escape. With no preparation owner this is the
    // ordinary unchanged path; these bytes are parsed later by the same reader.
    original.read_preparation_input(path)?;
    Ok(())
}

pub(crate) fn read_original_source_text(path: &Path) -> io::Result<Option<String>> {
    let Some(original) = ORIGINAL.get() else { return Ok(None) };
    let original = original
        .upgrade()
        .ok_or_else(|| io::Error::other("original source input owner expired"))?;
    original.read_preparation_input(path)
}

#[cfg(test)]
mod tests;
