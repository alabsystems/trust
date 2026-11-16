//! Trust: actual original source/output custody before Bootstrap configuration.
//! Progress is data; this owner has no normal WITHHELD release or SDK constructor.
use std::ffi::OsString;
use std::mem::ManuallyDrop;
use std::path::Path;

use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, OriginalSourceRoot, ProtectedWorkScope,
};
use trust_resource_controller::bootstrap_graph::preparation;
use trust_resource_controller::client::bootstrap_graph::{
    InputWorkClosed, ResidentDependencyInputs,
};

use super::*;

mod compilation;
pub(super) mod preparation_inputs;
pub use compilation::{
    OriginalBootstrapCompilation, OriginalBootstrapMember, OriginalBootstrapMemberFailure,
    RetiredOriginalBootstrapMember,
};
pub(crate) use compilation::{OriginalBootstrapConfiguration, Stage0Selection};
pub use preparation_inputs::{OriginalPreparationInputs, OriginalPreparationSource};

use crate::core::build_steps::frontend_runtime::{BuildOwnership, CommandOwnership};
use crate::core::config::{Config, InputLayout};

pub(super) struct OwnedInputs {
    command: Arc<CommandOwnership>,
    output: Arc<BuildOwnership>,
    scope: Mutex<Option<ProtectedWorkScope>>,
    source: OnceLock<Arc<OriginalSourceRoot>>,
    deadline: Instant,
}
/// Actual unused source lease held while the canonical parser selects output.
/// No source withholding or output availability is inferred from layout DATA.
struct SourceInputs {
    command: Arc<CommandOwnership>,
    deadline: Instant,
}
impl SourceInputs {
    fn acquire(source: &Path, deadline: Instant) -> io::Result<Self> {
        time(deadline)?;
        if !source.is_absolute() || source.canonicalize()? != source {
            return Err(io::Error::other(
                "dependency inputs require the original canonical source",
            ));
        }
        let manager = Manager::open(source)?;
        let lease = match manager.acquire_lease(&Acquire {
            kind: Kind::Build, owner_pid: std::process::id(),
            purpose: "native original-Root dependency inputs".into(),
            contract: "the complete source-declared dependency envelope retains these actual source and output owners".into(),
            wait: Duration::ZERO, inherited_token: None, break_reason: None,
        })? {
            LeaseAcquisition::Granted(lease) if !lease.is_borrowed() => lease,
            LeaseAcquisition::Granted(_) => return Err(io::Error::other("dependency inputs cannot promote a borrowed source manager")),
            LeaseAcquisition::Busy(_) => return Err(io::Error::new(io::ErrorKind::WouldBlock, "original dependency source already has an owner")),
        };
        time(deadline)?;
        let command = Arc::new(CommandOwnership::new(lease));
        command.check_original_source(source).map_err(io::Error::other)?;
        Ok(Self { command, deadline })
    }
    fn bind_output(self, source: &Path, output: &Path) -> io::Result<OwnedInputs> {
        time(self.deadline)?;
        self.command.check_original_source(source).map_err(io::Error::other)?;
        if !output.is_absolute() {
            return Err(io::Error::other("dependency output must be absolute"));
        }
        let output =
            build_helper::trust_output_lock::OutputLock::try_acquire(output)?.ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::WouldBlock,
                    "original dependency output already has an owner",
                )
            })?;
        time(self.deadline)?;
        let output = Arc::new(
            BuildOwnership::new(Arc::new(output), Arc::clone(&self.command))
                .map_err(io::Error::other)?,
        );
        Ok(OwnedInputs {
            command: self.command,
            output,
            scope: Mutex::new(None),
            source: OnceLock::new(),
            deadline: self.deadline,
        })
    }
    fn select_xpy_output(
        self,
        source: &Path,
        arguments: &[OsString],
    ) -> io::Result<(OwnedInputs, InputLayout)> {
        self.select_xpy_output_at(source, arguments, &std::env::current_dir()?)
    }
    fn select_xpy_output_at(
        self,
        source: &Path,
        arguments: &[OsString],
        invocation: &Path,
    ) -> io::Result<(OwnedInputs, InputLayout)> {
        time(self.deadline)?;
        self.command.check_original_source(source).map_err(io::Error::other)?;
        let flags = crate::engine::xpy_flags(arguments)
            .map_err(io::Error::other)?
            .ok_or_else(|| io::Error::other("display has no original dependency input work"))?;
        if flags.dry_run
            || crate::utils::trust_preparation::PreparationScope::for_flags(&flags)
                != crate::utils::trust_preparation::PreparationScope::FullEnvelope
        {
            return Err(io::Error::other(
                "original x.py input work requires the actual full request",
            ));
        }
        // The real lease above precedes every layout read. The resulting paths
        // do not supply custody; acquire the actual output guard before protect.
        let selected = match &flags.src {
            Some(selected) => selected.clone(),
            None => super::native_git::discover_source_directory_at(invocation, self.deadline)?,
        };
        if selected.canonicalize()? != source {
            return Err(io::Error::other("native x.py layout selected a different source owner"));
        }
        let git_info = super::native_git::observe_profile(&selected, false, self.deadline, false)?;
        let layout = Config::input_layout_at_native_source(&flags, source, selected, git_info)?;
        time(self.deadline)?;
        self.command.check_original_source(source).map_err(io::Error::other)?;
        if layout.source().canonicalize()? != source {
            return Err(io::Error::other("native x.py layout selected a different source owner"));
        }
        let owned = self.bind_output(source, layout.output())?;
        Ok((owned, layout))
    }
}
impl OwnedInputs {
    fn acquire(source: &Path, output: &Path, deadline: Instant) -> io::Result<Self> {
        // Keep the closed dependency-input entry's original validation order:
        // no source Manager is acquired for a relative output selection.
        if !output.is_absolute() {
            return Err(io::Error::other("dependency output must be absolute"));
        }
        SourceInputs::acquire(source, deadline)?.bind_output(source, output)
    }
    fn protect(&self, source: &Path) -> io::Result<()> {
        self.command.check_original_source(source).map_err(io::Error::other)?;
        let original = self.command.withhold_original().map_err(io::Error::other)?;
        let scope = ProtectedWorkScope::new(original, self.deadline)?;
        let mut retained = lock(&self.scope, self.deadline)?;
        if retained.is_some() {
            return Err(io::Error::other("original dependency source scope is one-use"));
        }
        *retained = Some(scope);
        // Retain the actual protected owner BEFORE binding or exporting source.
        let source =
            Arc::new(retained.as_ref().expect("same actual scope").original_source(source)?);
        self.source
            .set(source)
            .map_err(|_| io::Error::other("original dependency source already bound"))?;
        self.output.check().map_err(io::Error::other)
    }
    pub(super) fn check(&self) -> io::Result<()> {
        time(self.deadline)?;
        self.output.check().map_err(io::Error::other)?;
        lock(&self.scope, self.deadline)?
            .as_ref()
            .ok_or_else(|| io::Error::other("actual dependency scope is absent"))?
            .check_current()?;
        self.source
            .get()
            .ok_or_else(|| io::Error::other("actual dependency source is absent"))?
            .check_current()
    }
}

/// Actual original inputs and the same immutable resident attempt. Paths and
/// observations cannot construct this value, and it never creates a new epoch.
pub struct OriginalDependencyInputs {
    graph: Arc<OriginalHostGraph>,
    owners: Arc<OwnedInputs>,
    request: preparation::Request,
    observation: Option<preparation::Observation>,
    xpy: Option<XpySelection>,
    // This actual snapshot retains graph/source/read descriptions. Ordinary
    // error, unwind and session Drop cannot release them before opaque native
    // closure plus all local joins. Only retire_closed explicitly takes it.
    // Session-local placement avoids Graph -> owners -> snapshot -> Graph.
    source_snapshot: ManuallyDrop<Option<DependencySourceSnapshot>>,
}
struct XpySelection {
    arguments: Vec<OsString>,
    layout: InputLayout,
}
impl OriginalHostGraph {
    /// Acquire real unused source/output guards before any Bootstrap Config.
    /// The graph itself must be this original managed entry's authenticated
    /// Root, SAME early scheduler and real pinned SDK/Host support.
    pub fn begin_dependency_inputs(
        self: &Arc<Self>,
        source: &Path,
        output: &Path,
        mode: preparation::Mode,
    ) -> io::Result<OriginalDependencyInputs> {
        self.prepare_dependency_entry()?;
        let owners = Arc::new(OwnedInputs::acquire(source, output, self.deadline)?);
        self.enroll_dependency_inputs(source, output, owners, mode, None)
    }

    /// Acquire the SAME real original source before canonical layout reads,
    /// then the selected actual output guard before Config/protect/enrollment.
    /// No Full compilation capability is supplied by these inputs or paths.
    pub fn begin_xpy_dependency_inputs(
        self: &Arc<Self>,
        source: &Path,
        arguments: Vec<OsString>,
        mode: preparation::Mode,
    ) -> io::Result<OriginalDependencyInputs> {
        self.prepare_dependency_entry()?;
        let original = SourceInputs::acquire(source, self.deadline)?;
        let (owners, layout) = original.select_xpy_output(source, &arguments)?;
        let output = layout.output().to_owned();
        self.enroll_dependency_inputs(
            source,
            &output,
            Arc::new(owners),
            mode,
            Some(XpySelection { arguments, layout }),
        )
    }

    fn prepare_dependency_entry(self: &Arc<Self>) -> io::Result<()> {
        self.check()?;
        {
            let state = lock(&self.state, self.deadline)?;
            if state.dependency_owners.is_some()
                || state.scope.is_some()
                || !matches!(state.phase, Some(Phase::Supported(_)))
            {
                return Err(io::Error::other(
                    "original dependency entry cannot replace an existing graph or source owner",
                ));
            }
        }
        Arc::clone(self).install().map_err(io::Error::other)?;
        Ok(())
    }

    fn enroll_dependency_inputs(
        self: &Arc<Self>,
        source: &Path,
        output: &Path,
        owners: Arc<OwnedInputs>,
        mode: preparation::Mode,
        xpy: Option<XpySelection>,
    ) -> io::Result<OriginalDependencyInputs> {
        {
            let mut state = lock(&self.state, self.deadline)?;
            if state.dependency_owners.is_some() || state.scope.is_some() || state.failed {
                return Err(io::Error::other(
                    "original dependency input owner is already retained or unresolved",
                ));
            }
            // Strong actual owners survive every subsequent publication,
            // enrollment, output delivery, I/O error and local session drop.
            state.dependency_owners = Some(Arc::clone(&owners));
        }
        owners.protect(source)?;
        let dispatch = lock(&owners.scope, self.deadline)?
            .as_ref()
            .ok_or_else(|| io::Error::other("missing actual dependency scope"))?
            .dispatcher();
        self.enroll_original_source(
            dispatch.downgrade(),
            Arc::clone(owners.source.get().expect("same actual source")),
            source,
            output,
        )
        .map_err(io::Error::other)?;
        // SAFETY: these are the SAME acquired OutputLock and command, retained
        // above before the close-only handoff to this actual original Host.
        let descriptions = unsafe { owners.output.original_output(&owners.command, output) }
            .map_err(io::Error::other)?;
        self.attach_output(&descriptions, Arc::clone(&owners.output), Arc::clone(&owners.command))
            .map_err(io::Error::other)?;
        owners.check()?;
        let mut operation = [0; 16];
        use std::io::Read as _;
        let mut random = File::open("/dev/urandom")?;
        while operation == [0; 16]
            || operation == self.key.graph
            || operation == self.key.query.call_attempt
            || operation == self.key.query.binding.root_attempt
        {
            random.read_exact(&mut operation)?;
        }
        let state = lock(&self.state, self.deadline)?;
        let timeout = self
            .deadline
            .checked_duration_since(Instant::now())
            .ok_or(io::ErrorKind::TimedOut)?
            .as_nanos()
            .min(u128::from(preparation::MAX_WORK_NS));
        let request = preparation::Request {
            key: query::OperationKey {
                graph: self.key.clone(),
                sequence: state.sequence,
                operation,
            },
            mode,
            timeout_ns: u64::try_from(timeout)
                .map_err(|_| io::Error::other("dependency work bound exceeds wire range"))?,
        };
        request.validate()?;
        drop(state); // Snapshot checks reenter this SAME graph; never hold its mutex.
        let mut inputs = OriginalDependencyInputs {
            graph: Arc::clone(self),
            owners,
            request,
            observation: None,
            xpy,
            source_snapshot: ManuallyDrop::new(None),
        };
        match self.dependency_source_snapshot() {
            Ok(snapshot) => *inputs.source_snapshot = Some(snapshot),
            Err(refusal) => {
                let (error, snapshot) = refusal.into_parts();
                // Preserve even a partially captured SAME original before
                // returning an error or allowing the caller to drop it.
                *inputs.source_snapshot = Some(*snapshot);
                return Err(inputs.retained_error(error));
            }
        }
        if let Err(error) = inputs.check_current() {
            return Err(inputs.retained_error(error));
        }
        Ok(inputs)
    }
}
impl OriginalDependencyInputs {
    fn retained_error(self, error: io::Error) -> io::Error {
        if let Ok(mut state) = lock(&self.graph.state, self.graph.deadline) {
            state.failed = true;
        }
        io::Error::new(error.kind(), RefusedDependencyInputs::new(error, self))
    }

    /// Original full request DATA retained by the actual source/output owner.
    /// This accessor grants no Full engine, native member or release authority.
    pub fn xpy_selection(&self) -> Option<(&[OsString], &InputLayout)> {
        self.xpy.as_ref().map(|selected| (selected.arguments.as_slice(), &selected.layout))
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.owners.check()?;
        self.graph.check()?;
        self.source_snapshot
            .as_ref()
            .ok_or_else(|| io::Error::other("actual dependency source snapshot is absent"))?
            .check_current()
    }
    pub fn original_source(&self) -> io::Result<&Arc<OriginalSourceRoot>> {
        self.check_current()?;
        self.owners
            .source
            .get()
            .ok_or_else(|| io::Error::other("actual original dependency source is absent"))
    }
    pub fn original_scheduler(&self) -> &Jobserver {
        &self.graph.original_scheduler
    }
    pub fn original_deadline(&self) -> Instant {
        self.graph.deadline
    }
    pub fn request(&self) -> &preparation::Request {
        &self.request
    }
    pub fn observation(&self) -> Option<&preparation::Observation> {
        self.observation.as_ref()
    }
    /// Same actual lexical owner, compatible with a non-Send Cargo context.
    /// It grants no extra CPU or native child rights; those remain original.
    pub fn scoped_input_work<T>(&self, work: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
        self.check_current()?;
        let dispatch = lock(&self.owners.scope, self.graph.deadline)?
            .as_ref()
            .ok_or_else(|| io::Error::other("actual dependency scope already consumed"))?
            .dispatcher();
        let result = dispatch.scoped_threads(|_| work())?;
        if let Err(error) = self.check_current() {
            // A returned value may retain the actual native library input
            // continuation and need not be Send. Preserve it on uncertainty.
            std::mem::forget(result);
            return Err(error);
        }
        result
    }
    /// Reconnect only the SAME request. No revision/phase/count is authority.
    pub fn observe(&mut self) -> io::Result<preparation::Observation> {
        self.check_current()?;
        let deadline = Instant::now()
            .checked_add(Duration::from_secs(8))
            .ok_or_else(|| io::Error::other("dependency observation deadline overflow"))?
            .min(self.graph.deadline);
        let mut state = lock(&self.graph.state, deadline)?;
        let State { client, phase, .. } = &mut *state;
        let Some(Phase::OutputBound(original)) = phase else {
            return Err(io::Error::other(
                "dependency input observation lost actual output-bound enrollment",
            ));
        };
        let observation = original.dependency_inputs(client, self.request.clone(), deadline)?;
        self.observation = Some(observation.clone());
        drop(state);
        self.check_current()?;
        Ok(observation)
    }
}

impl OriginalDependencyInputs {
    /// Open only the SAME actually prepared native input session.
    pub fn input_work(&mut self) -> io::Result<ResidentDependencyInputs> {
        self.check_current()?;
        let deadline = self.graph.deadline;
        let mut state = lock(&self.graph.state, deadline)?;
        let State { client, phase, .. } = &mut *state;
        let Some(Phase::OutputBound(original)) = phase else {
            return Err(io::Error::other("original output-bound input owner is absent"));
        };
        let result = original.dependency_input_work(client, &self.request, deadline);
        drop(state);
        let current = self.check_current();
        match (result, current) {
            (Ok(work), Ok(())) => Ok(work),
            (Ok(work), Err(error)) => {
                Err(io::Error::new(error.kind(), RefusedDependencyInputs::new(error, work)))
            }
            (Err(error), _) => Err(error),
        }
    }

    /// Consume the actual completed library session, close the original native
    /// enrollment, join local work, and retire only this exact original source.
    /// Any refusal owns every remaining actual input; status is never closure.
    pub fn finish(
        self,
        work: ResidentDependencyInputs,
    ) -> Result<RetiredOriginalDependencyInputs, RefusedDependencyInputs> {
        let close = (|| {
            self.check_current()?;
            let mut state = lock(&self.graph.state, self.graph.deadline)?;
            let State { client, phase, .. } = &mut *state;
            let Some(Phase::OutputBound(original)) = phase else {
                return Err(io::Error::other("original input enrollment is absent"));
            };
            original.finish_dependency_input_work(client, work, self.graph.deadline)
        })();
        let closed = match close {
            Ok(closed) => closed,
            Err(error) => return Err(RefusedDependencyInputs::new(error, self)),
        };
        self.retire_closed(closed)
    }

    // Trust: component and Full consume the SAME actual native source-work
    // witness and local join/retirement path. Neither status nor a Frame enters.
    fn retire_closed(
        self,
        closed: InputWorkClosed,
    ) -> Result<RetiredOriginalDependencyInputs, RefusedDependencyInputs> {
        if closed.attempt() != &self.request || closed.source().key != self.graph.key {
            return Err(RefusedDependencyInputs::new(
                io::Error::other("native input closure differs from the same original attempt"),
                (self, closed),
            ));
        }
        let gnu = match witnesses(&self.graph.original_scheduler) {
            Ok((_, gnu)) => gnu,
            Err(error) => return Err(RefusedDependencyInputs::new(error, (self, closed))),
        };
        let (source, offer) = {
            // Keep the lock borrow on this same Arc clone so a refused lock
            // can retain the entire consumed session without moving a borrow.
            let graph = Arc::clone(&self.graph);
            let mut state = match lock(&graph.state, graph.deadline) {
                Ok(state) => state,
                Err(error) => return Err(RefusedDependencyInputs::new(error, (self, closed))),
            };
            if state.failed
                || state.source.is_none()
                || state.source_offer.is_none()
                || state.source_task_active
                || !state.objects.is_empty()
                || state.compilation.is_some()
                || state.compilation_failure.is_some()
            {
                drop(state);
                return Err(RefusedDependencyInputs::new(
                    io::Error::other(
                        "native closure still has unrelated or absent local source inputs",
                    ),
                    (self, closed),
                ));
            }
            let source = state.source.take().expect("checked same actual source");
            let offer = state.source_offer.take().expect("checked same actual offer");
            state.scope = None;
            state.output_owner = None;
            state.command_owner = None;
            state.dependency_owners = None;
            state.phase = None;
            (source, offer)
        };
        let Self { graph, owners, request, mut source_snapshot, .. } = self;
        let owned = match Arc::try_unwrap(owners) {
            Ok(owned) => owned,
            Err(owners) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("original input owner still has a local borrower"),
                    (graph, owners, source_snapshot, source, offer, closed),
                ));
            }
        };
        let OwnedInputs { command, output, scope, source: extra_source, .. } = owned;
        drop(extra_source);
        let scope = match scope.into_inner() {
            Ok(Some(scope)) => scope,
            Ok(None) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("original protected scope was already consumed"),
                    (graph, command, output, source_snapshot, source, offer, closed),
                ));
            }
            Err(poison) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("original protected scope was poisoned"),
                    (
                        graph,
                        command,
                        output,
                        source_snapshot,
                        poison.into_inner(),
                        source,
                        offer,
                        closed,
                    ),
                ));
            }
        };
        let local = match join_local_inputs(scope, command, output) {
            Ok(local) => local,
            Err(failure) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("actual original local input scope did not join"),
                    (graph, failure, source_snapshot, source, offer, closed),
                ));
            }
        };
        // Native enrollment is consumed and the actual scope is JOINED. Keep
        // every snapshot guard through those joins, then use only the typed
        // closed/joined validation path; OPEN graph/source checks are invalid.
        let final_check = source_snapshot
            .as_ref()
            .ok_or_else(|| io::Error::other("actual dependency source snapshot was lost"))
            .and_then(|snapshot| {
                snapshot.check_joined(&graph, &request, &source, &local.joined, &offer, &closed)
            });
        if let Err(error) = final_check {
            return Err(RefusedDependencyInputs::new(
                error,
                (graph, local, source_snapshot, source, offer, closed),
            ));
        }
        // This is the sole explicit disposal of the retained snapshot: both
        // actual native closure and all local joins/final bookends succeeded.
        drop(source_snapshot.take());
        let source = match Arc::try_unwrap(source) {
            Ok(source) => source,
            Err(source) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("original source still has a local borrower"),
                    (graph, local, source, offer, closed),
                ));
            }
        };
        let JoinedLocalInputs { joined, command, output } = local;
        let output = match Arc::try_unwrap(output) {
            Ok(output) => output,
            Err(output) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("actual output guard still has another local borrower"),
                    (graph, joined, command, output, source, offer, closed),
                ));
            }
        };
        let (output, output_command) = output.into_resident_output();
        // The SAME original WITHHELD lease remains in joined/source/offer.
        // Drop only duplicate command references required by its unique handoff;
        // the actual output kernel lock remains held through retirement/refusal.
        drop(output_command);
        drop(command);
        match joined.retire_resident_inputs(source, offer, closed) {
            Ok(retired) => Ok(RetiredOriginalDependencyInputs { graph, gnu, retired }),
            Err(refusal) => Err(RefusedDependencyInputs::new(
                io::Error::other(refusal.error().to_string()),
                (graph, output, refusal),
            )),
        }
    }
}

/// Final checks of the original Root after successful consumed native/local
/// source retirement. No constructor from a phase, status or saved record.
/// Active graph/query operations remain permanently unavailable after close.
#[must_use]
pub struct RetiredOriginalDependencyInputs {
    graph: Arc<OriginalHostGraph>,
    gnu: GnuIdentity,
    retired: build_helper::trust_repo_lock::management::RetiredResidentInputs,
}
impl RetiredOriginalDependencyInputs {
    pub fn belongs_to(&self, graph: &Arc<OriginalHostGraph>) -> bool {
        Arc::ptr_eq(&self.graph, graph)
    }
    pub fn check_current(&self) -> io::Result<()> {
        let deadline = Instant::now()
            .checked_add(Duration::from_secs(8))
            .ok_or_else(|| io::Error::other("retired input check deadline overflow"))?
            .min(self.graph.deadline);
        time(deadline)?;
        self.retired.check_current(deadline)?;
        gnu_check(&self.graph.original_scheduler, &self.gnu)?;
        let state = lock(&self.graph.state, deadline)?;
        if state.failed
            || state.failure.is_some()
            || state.graph_failure.is_some()
            || state.object_failure.is_some()
            || state.phase.is_some()
            || state.scope.is_some()
            || state.source.is_some()
            || state.source_offer.is_some()
            || state.source_task_active
            || !state.objects.is_empty()
            || state.output_owner.is_some()
            || state.command_owner.is_some()
            || state.dependency_owners.is_some()
            || state.compilation.is_some()
            || state.compilation_failure.is_some()
        {
            return Err(io::Error::other("retired input graph has unresolved actual borrowers"));
        }
        drop(state);
        self.retired.check_current(deadline)?;
        time(deadline)
    }
}

struct JoinedLocalInputs {
    joined: build_helper::trust_repo_lock::management::LocalJoinedScope,
    command: Arc<CommandOwnership>,
    output: Arc<BuildOwnership>,
}
struct RefusedLocalInputs {
    _failure: build_helper::trust_repo_lock::management::ScopeFailure,
    _command: Arc<CommandOwnership>,
    _output: Arc<BuildOwnership>,
}
fn join_local_inputs(
    scope: ProtectedWorkScope,
    command: Arc<CommandOwnership>,
    output: Arc<BuildOwnership>,
) -> Result<JoinedLocalInputs, RefusedLocalInputs> {
    match scope.seal().join() {
        Ok(joined) => Ok(JoinedLocalInputs { joined, command, output }),
        Err(failure) => {
            Err(RefusedLocalInputs { _failure: failure, _command: command, _output: output })
        }
    }
}

/// An unresolved native/local input continuation retains its real owners.
#[must_use]
pub struct RefusedDependencyInputs {
    error: io::Error,
    _retained: Box<dyn std::any::Any + Send + Sync>,
}
impl RefusedDependencyInputs {
    fn new(error: io::Error, retained: impl std::any::Any + Send + Sync) -> Self {
        Self { error, _retained: Box::new(retained) }
    }
}
impl std::fmt::Debug for RefusedDependencyInputs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefusedDependencyInputs")
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for RefusedDependencyInputs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for RefusedDependencyInputs {}

#[cfg(test)]
mod tests;
