//! The original native Bootstrap Root's restrictive command owner. This is
//! installed before Config, uses the SAME captured scheduler, and has no local
//! spawn, graph-close, runtime-completion or manager-release constructor.

use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io;
use std::os::fd::{AsFd, AsRawFd as _, OwnedFd};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{FileExt as _, MetadataExt as _, OpenOptionsExt as _};
use std::process::{Command, ExitStatus, Output};
use std::sync::{Arc, Mutex, OnceLock, TryLockError, Weak};
use std::time::{Duration, Instant};

use jobserver_utils::Jobserver;
use sha2::{Digest as _, Sha256};
use trust_resource_controller::bootstrap_graph::{
    Enrollment, GnuIdentity, Key, OutputAttachment, SourceAttachment, SourceRecord, query,
};
use trust_resource_controller::client::Client;
use trust_resource_controller::client::bootstrap_graph::{
    BootstrapGraphSupport, CompletedSdkQuery, EnrolledBootstrapGraph, GraphFailure,
    OutputBoundBootstrapGraph, QueryFailure, SourceBoundBootstrapGraph,
};
use trust_resource_controller::{ContextReply, FileIdentity, MetadataFile, Outcome, Status};

// Permanent restriction after installation, without retaining the only actual
// owner forever. Expired/failed upgrade refuses rather than restoring spawn.
static ORIGINAL: OnceLock<Weak<OriginalHostGraph>> = OnceLock::new();
mod dependency_inputs;
mod native_git;
pub(crate) use dependency_inputs::preparation_inputs::{
    begin_original_configuration_parse, check_original_configuration_path,
    read_original_source_text, with_original_configuration,
};
pub use dependency_inputs::{
    OriginalBootstrapCompilation, OriginalBootstrapMember, OriginalBootstrapMemberFailure,
    OriginalDependencyInputs, OriginalPreparationInputs, OriginalPreparationSource,
    RetiredOriginalBootstrapMember, RetiredOriginalDependencyInputs,
};
pub(crate) use dependency_inputs::{OriginalBootstrapConfiguration, Stage0Selection};
pub use native_git::{
    CommittedEntry, CommittedLookup, CommittedRepository, CommittedSourceReadSet,
    DependencySourceRefusal, DependencySourceSnapshot, SourceRead,
};
pub(crate) mod object;
pub(crate) use native_git::{native_git_info, native_source_directory, native_source_git_info};
pub(crate) use object::produce_native_object;

pub struct OriginalHostGraph {
    state: Mutex<State>,
    original_scheduler: Jobserver,
    deadline: Instant,
    key: Key,
    context: ContextReply,
}
struct State {
    client: Client,
    phase: Option<Phase>,
    sequence: u64,
    completed: Vec<CompletedSdkQuery>,
    failure: Option<QueryFailure>,
    graph_failure: Option<GraphFailure>,
    scope: Option<build_helper::trust_repo_lock::management::WeakScopeDispatch>,
    failed: bool,
    input_deadline: Instant,
    preparation_inputs: Option<Arc<dependency_inputs::preparation_inputs::Inputs>>,
    preparation_source: Option<Arc<dependency_inputs::preparation_inputs::SourceStage>>,
    source: Option<Arc<build_helper::trust_repo_lock::management::OriginalSourceRoot>>,
    source_offer: Option<build_helper::trust_repo_lock::management::OriginalSourceOffer>,
    output_owner: Option<Arc<crate::core::build_steps::frontend_runtime::BuildOwnership>>,
    command_owner: Option<Arc<crate::core::build_steps::frontend_runtime::CommandOwnership>>,
    source_task_active: bool,
    source_tasks: Vec<Arc<object::source_task::Attempt>>,
    objects: Vec<object::OriginalObject>,
    object_failure: Option<trust_resource_controller::client::bootstrap_graph::ObjectFailure>,
    dependency_owners: Option<Arc<dependency_inputs::OwnedInputs>>,
    compilation: Option<
        Arc<trust_resource_controller::client::bootstrap_graph::ResidentBootstrapCompilation>,
    >,
    compilation_failure:
        Option<trust_resource_controller::client::bootstrap_graph::RefusedCompilationAdvance>,
}
enum Phase {
    Supported(Box<BootstrapGraphSupport>),
    Enrolled(Box<EnrolledBootstrapGraph>),
    SourceBound(Box<SourceBoundBootstrapGraph>),
    OutputBound(Box<OutputBoundBootstrapGraph>),
}
impl Phase {
    fn check(&self, client: &Client, deadline: Instant) -> io::Result<()> {
        match self {
            Self::Supported(support) => {
                client.revalidate_bootstrap_graph_support(support, deadline)
            }
            Self::Enrolled(original) => original.revalidate(deadline),
            Self::SourceBound(original) => original.revalidate(deadline),
            Self::OutputBound(original) => original.revalidate(deadline),
        }
    }
    fn query(
        &mut self,
        client: &Client,
        request: query::Request,
        descriptions: &[std::os::fd::BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> Result<CompletedSdkQuery, QueryFailure> {
        match self {
            Self::Supported(support) => {
                client.bootstrap_sdk_query(support, request, descriptions, deadline)
            }
            Self::Enrolled(original) => original.sdk_query(client, request, descriptions, deadline),
            Self::SourceBound(original) => {
                original.sdk_query(client, request, descriptions, deadline)
            }
            Self::OutputBound(original) => {
                original.sdk_query(client, request, descriptions, deadline)
            }
        }
    }
}
fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
fn lock<T>(mutex: &Mutex<T>, deadline: Instant) -> io::Result<std::sync::MutexGuard<'_, T>> {
    loop {
        time(deadline)?;
        match mutex.try_lock() {
            Ok(guard) => return Ok(guard),
            Err(TryLockError::Poisoned(_)) => {
                return Err(io::Error::other("original native Bootstrap owner is poisoned"));
            }
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(2)),
        }
    }
}
impl OriginalHostGraph {
    /// # Safety
    /// Only the original managed Targo entry may supply its SAME early captured
    /// GNU owner and actual Client/opaque support. No fresh Jobserver, count,
    /// borrowed build holder, context data or environment reimport qualifies.
    /// The actual Host must still enforce its original Job and native borrower.
    pub unsafe fn from_original_root(
        client: Client,
        support: BootstrapGraphSupport,
        original_scheduler: Jobserver,
    ) -> io::Result<Self> {
        let deadline = support.original_deadline();
        client.revalidate_bootstrap_graph_support(&support, deadline)?;
        let (_, gnu) = witnesses(&original_scheduler)?;
        gnu_check(&original_scheduler, &gnu)?;
        time(deadline)?;
        let key = support.key().clone();
        let context = support.observation().clone();
        Ok(Self {
            state: Mutex::new(State {
                client,
                phase: Some(Phase::Supported(Box::new(support))),
                sequence: 1,
                completed: vec![],
                failure: None,
                graph_failure: None,
                scope: None,
                failed: false,
                input_deadline: deadline,
                preparation_inputs: None,
                preparation_source: None,
                source: None,
                source_offer: None,
                output_owner: None,
                command_owner: None,
                source_task_active: false,
                source_tasks: vec![],
                objects: vec![],
                object_failure: None,
                dependency_owners: None,
                compilation: None,
                compilation_failure: None,
            }),
            original_scheduler,
            deadline,
            key,
            context,
        })
    }
    pub(crate) fn install(self: Arc<Self>) -> Result<(), String> {
        self.check().map_err(|error| error.to_string())?;
        super::install_original(self.original_scheduler.clone())?;
        ORIGINAL
            .set(Arc::downgrade(&self))
            .map_err(|_| "native Bootstrap graph was already installed".to_owned())
    }
    pub fn original_deadline(&self) -> Instant {
        self.deadline
    }
    fn input_deadline(&self) -> io::Result<Instant> {
        let deadline = lock(&self.state, self.deadline)?.input_deadline.min(self.deadline);
        time(deadline)?;
        Ok(deadline)
    }
    pub fn check(&self) -> io::Result<()> {
        let state = lock(&self.state, self.deadline)?;
        let deadline = state.input_deadline.min(self.deadline);
        if state.failed || state.source_task_active {
            return Err(io::Error::other("original Bootstrap graph has an unresolved operation"));
        }
        scope_current(&state)?;
        if let Some(compilation) = &state.compilation {
            let observation = Instant::now()
                .checked_add(Duration::from_secs(8))
                .ok_or_else(|| io::Error::other("compilation observation deadline overflow"))?
                .min(self.deadline);
            compilation.check_current(observation)?;
        } else {
            state
                .phase
                .as_ref()
                .ok_or_else(|| io::Error::other("original graph transition is unresolved"))?
                .check(&state.client, deadline)?;
        }
        time(deadline)
    }
    fn output(&self, command: &mut Command, stdout: bool, stderr: bool) -> io::Result<Output> {
        // Trust: Advance seals the SDK query state. Full command I/O belongs
        // only to the executor retaining the SAME concrete producer guards;
        // never reenter a public query or hold this mutex across its work.
        let compilation = lock(&self.state, self.deadline)?.compilation.is_some();
        if compilation {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "Full commands require the maintained wrapper's complete input projection",
            ));
        }
        let mut original = lock(&super::selected()?.state, self.deadline)?;
        if original.producer_failed || !original.embedded_original {
            return Err(io::Error::other("native graph needs its same original scheduler"));
        }
        let mut state = lock(&self.state, self.deadline)?;
        if state.failed || state.source_task_active {
            return Err(io::Error::other("original native command graph is unresolved"));
        }
        scope_current(&state)?;
        // Restrict before every fallible native operation. No error/unwind can
        // silently restore ordinary spawning or return an implicit borrower.
        state.failed = true;
        original.producer_failed = true;
        if state.completed.len() >= 4096 {
            return Err(io::Error::other("complete native query census exceeds its bound"));
        }
        let server = original
            .server
            .as_ref()
            .ok_or_else(|| io::Error::other("original GNU owner missing"))?;
        let (descriptions, gnu) = witnesses(server)
            .map_err(|error| preparation_error("original GNU witnesses", None, error))?;
        let request =
            request(command, &self.context, &self.key, state.sequence, gnu, self.deadline)
                .map_err(|error| preparation_error("SDK request construction", None, error))?;
        let result = {
            let State { client, phase, .. } = &mut *state;
            phase
                .as_mut()
                .ok_or_else(|| io::Error::other("original graph transition is unresolved"))?
                .query(client, request, &descriptions.each_ref().map(AsFd::as_fd), self.deadline)
        };
        let completed = match result {
            Ok(completed) => completed,
            Err(failure) => {
                let error = io::Error::other(format!("native SDK query failed: {failure}"));
                state.failure = Some(failure);
                return Err(error);
            }
        };
        // Retain before any later fallible status/output/IO operation.
        state.completed.push(completed);
        let observation =
            state.completed.last().expect("same actual completed query").observation();
        let status = observed_status(&observation.completion.finished.status)?;
        let unchanged = observation.completion.inputs_unchanged.is_ok();
        let output = Output {
            status,
            stdout: if stdout { observation.stdout.clone() } else { vec![] },
            stderr: if stderr { observation.stderr.clone() } else { vec![] },
        };
        if !stdout {
            use std::io::Write as _;
            std::io::stdout().write_all(&observation.stdout)?;
        }
        if !stderr {
            use std::io::Write as _;
            std::io::stderr().write_all(&observation.stderr)?;
        }
        // Keep the actual opaque query owner, including its original accepted
        // pin and complete output DATA, through this Root's graph lifetime.
        time(self.deadline)?;
        if !unchanged {
            return Err(io::Error::other("original SDK query inputs changed"));
        }
        if !status.success() {
            return Ok(output);
        }
        state.sequence = state
            .sequence
            .checked_add(1)
            .ok_or_else(|| io::Error::other("native query sequence exhausted"))?;
        state.failed = false;
        original.producer_failed = false;
        Ok(output)
    }

    pub(crate) fn enroll(
        &self,
        scope: &crate::engine::ExecutionScope,
        source: &std::path::Path,
        output: &std::path::Path,
    ) -> Result<(), String> {
        scope.check_current()?;
        self.enroll_original_source(
            scope.weak_dispatch()?,
            Arc::clone(scope.original_source_root()?),
            source,
            output,
        )
    }

    fn enroll_original_source(
        &self,
        dispatch: build_helper::trust_repo_lock::management::WeakScopeDispatch,
        original_source: Arc<build_helper::trust_repo_lock::management::OriginalSourceRoot>,
        source: &std::path::Path,
        output: &std::path::Path,
    ) -> Result<(), String> {
        dispatch
            .upgrade()
            .and_then(|scope| scope.check_current())
            .map_err(|error| error.to_string())?;
        original_source.check_current().map_err(|error| error.to_string())?;
        let result = (|| {
            let mut scheduler = lock(&super::selected()?.state, self.deadline)?;
            if scheduler.producer_failed || !scheduler.embedded_original {
                return Err(io::Error::other(
                    "native enrollment needs its same original scheduler",
                ));
            }
            let mut state = lock(&self.state, self.deadline)?;
            if state.failed || state.source_task_active {
                return Err(io::Error::other("original graph is unresolved"));
            }
            if state.scope.is_some() {
                return Err(io::Error::other("original graph scope is already bound"));
            }
            state.failed = true;
            scheduler.producer_failed = true;
            state.scope = Some(dispatch);
            state.source = Some(original_source);
            let (descriptions, gnu) = witnesses(
                scheduler
                    .server
                    .as_ref()
                    .ok_or_else(|| io::Error::other("original GNU owner missing"))?,
            )?;
            let Some(Phase::Supported(support)) = state.phase.take() else {
                return Err(io::Error::other("original graph enrollment is one-use"));
            };
            let request = Enrollment {
                key: self.key.clone(),
                source: source.as_os_str().as_bytes().to_vec(),
                output: output.as_os_str().as_bytes().to_vec(),
                gnu,
            };
            match state.client.enroll_bootstrap_graph(
                *support,
                request,
                &descriptions.each_ref().map(AsFd::as_fd),
                self.deadline,
            ) {
                Ok(original) => state.phase = Some(Phase::Enrolled(Box::new(original))),
                Err(error) => {
                    state.graph_failure = Some(error);
                    return Err(io::Error::other(
                        "original Bootstrap enrollment failed; custody retained",
                    ));
                }
            }
            // Retain the opaque producer BEFORE delivery. The exporter can
            // only duplicate the SAME original Manager/holder/record OFDs;
            // no path, decoded frame or received FD can create this owner.
            let offer =
                state.source.as_ref().expect("same bound source root").close_only_offer()?;
            if offer.deadline() != self.deadline {
                return Err(io::Error::other(
                    "source offer must retain the same original Root deadline",
                ));
            }
            let deadline = self.deadline;
            state.source_offer = Some(offer);
            let Some(Phase::Enrolled(original)) = state.phase.take() else {
                return Err(io::Error::other("original source attachment requires its enrollment"));
            };
            let attached =
                state.source_offer.as_ref().unwrap().with_descriptions(|files, data| {
                    let request = source_request(&self.key, data);
                    // SAFETY: the only input is the opaque original offer above,
                    // retained in State across all success/failure/unwind paths.
                    // Its callback bookends the complete exchange under its own
                    // unchanged deadline; the receiver holds close-only copies.
                    Ok(unsafe { (*original).attach_original_source(request, &files, deadline) })
                })?;
            match attached {
                Ok(original) => state.phase = Some(Phase::SourceBound(Box::new(original))),
                Err(error) => {
                    state.graph_failure = Some(error);
                    return Err(io::Error::other(
                        "original Bootstrap source attachment failed; custody retained",
                    ));
                }
            }
            scope_current(&state)?;
            time(self.deadline)?;
            state.failed = false;
            scheduler.producer_failed = false;
            Ok(())
        })();
        result.map_err(|error: io::Error| error.to_string())
    }

    pub(crate) fn attach_output(
        &self,
        descriptions: &build_helper::trust_output_lock::OriginalOutputDescriptions<'_>,
        output_owner: Arc<crate::core::build_steps::frontend_runtime::BuildOwnership>,
        command_owner: Arc<crate::core::build_steps::frontend_runtime::CommandOwnership>,
    ) -> Result<(), String> {
        let deadline = lock(&self.state, self.deadline)
            .map_err(|error| error.to_string())?
            .input_deadline
            .min(self.deadline);
        let result = (|| {
            let mut scheduler = lock(&super::selected()?.state, deadline)?;
            if scheduler.producer_failed || !scheduler.embedded_original {
                return Err(io::Error::other(
                    "native output attachment needs its same original scheduler",
                ));
            }
            let mut state = lock(&self.state, deadline)?;
            if state.failed || state.source_task_active {
                return Err(io::Error::other("original graph is unresolved"));
            }
            scope_current(&state)?;
            state.failed = true;
            scheduler.producer_failed = true;
            if state.output_owner.is_some() || state.command_owner.is_some() {
                return Err(io::Error::other("original output owners already attached"));
            }
            // Retain the actual typed originals BEFORE any output delivery.
            state.output_owner = Some(output_owner);
            state.command_owner = Some(command_owner);
            let Some(Phase::SourceBound(original)) = state.phase.take() else {
                return Err(io::Error::other(
                    "original output attachment requires its same enrollment",
                ));
            };
            // Paths check agreement only. The same actual close-only guard and
            // borrowed descriptions, retained by ExecutionScope, are custody.
            let output =
                std::path::Path::new(std::ffi::OsStr::from_bytes(&original.enrollment().output));
            if std::fs::canonicalize(output)? != descriptions.root() {
                // Keep the accepted original even on a pre-offer disagreement.
                state.phase = Some(Phase::SourceBound(original));
                return Err(io::Error::other(
                    "original output guard differs from its enrolled output",
                ));
            }
            let request = OutputAttachment {
                key: self.key.clone(),
                root: fd_identity(descriptions.directory())?,
                lock: fd_identity(descriptions.lock())?,
            };
            // SAFETY: ExecutionScope supplies only borrowed originals from its
            // SAME acquired BuildOwnership, after the same Manager was withheld
            // and enrolled. Both guard and original Host remain retained; the
            // Host only stores close-only duplicates through native settlement.
            let attached = unsafe {
                (*original).attach_original_output(
                    request,
                    &[descriptions.directory(), descriptions.lock()],
                    deadline,
                )
            };
            match attached {
                Ok(original) => state.phase = Some(Phase::OutputBound(Box::new(original))),
                Err(error) => {
                    state.graph_failure = Some(error);
                    return Err(io::Error::other(
                        "original Bootstrap output attachment failed; custody retained",
                    ));
                }
            }
            time(deadline)?;
            scope_current(&state)?;
            state.failed = false;
            scheduler.producer_failed = false;
            Ok(())
        })();
        result.map_err(|error: io::Error| error.to_string())
    }
}

pub(crate) fn installed() -> bool {
    ORIGINAL.get().is_some()
}
pub(crate) fn refuse_streaming() -> io::Error {
    if let Some(original) = ORIGINAL.get().and_then(Weak::upgrade)
        && let Ok(mut state) = lock(&original.state, original.deadline)
    {
        state.failed = true;
    }
    io::Error::new(
        io::ErrorKind::Unsupported,
        "native Bootstrap streaming producer has no qualified original Host operation",
    )
}
pub(crate) fn output(
    command: &mut Command,
    stdout: bool,
    stderr: bool,
) -> Option<io::Result<Output>> {
    ORIGINAL.get().map(|original| match original.upgrade() {
        Some(original) => original.output(command, stdout, stderr),
        None => Err(io::Error::other("original native Bootstrap graph owner is unavailable")),
    })
}

pub(crate) fn projected_output(
    command: &Command,
    stdout: bool,
    stderr: bool,
    inputs: crate::utils::exec::OriginalCommandInputs,
) -> Option<io::Result<Output>> {
    compilation_graph().map(|actual| {
        let actual = actual?;
        crate::engine::full_command_output(&actual, command, inputs, stdout, stderr)
    })
}

/// Only an actual advanced graph can provide a completed library command.
/// Query-only/expired installation never falls through to standalone spawn.
pub(crate) fn projected_stream(
    command: &Command,
    stdout: bool,
    stderr: bool,
    inputs: crate::utils::exec::OriginalCommandInputs,
) -> Option<io::Result<crate::engine::CompletedCommand>> {
    compilation_graph().map(|actual| {
        let actual = actual?;
        crate::engine::full_command_completed(&actual, command, inputs, stdout, stderr)
    })
}

fn compilation_graph() -> Option<io::Result<Arc<OriginalHostGraph>>> {
    let original = ORIGINAL.get()?;
    let actual = match original.upgrade() {
        Some(actual) => actual,
        None => return Some(Err(io::Error::other("original Full graph owner is closed"))),
    };
    let compilation = match lock(&actual.state, actual.deadline) {
        Ok(state) => state.compilation.is_some(),
        Err(error) => return Some(Err(error)),
    };
    compilation.then_some(Ok(actual))
}

fn source_request(
    key: &Key,
    data: &build_helper::trust_repo_lock::management::SourceOfferData,
) -> SourceAttachment {
    let metadata = data.description_metadata();
    let identity =
        |index: usize| FileIdentity { device: metadata[index].dev(), inode: metadata[index].ino() };
    let record = |index: usize, bytes: &[u8]| SourceRecord {
        identity: identity(index),
        bytes: bytes.len() as u64,
        sha256: Sha256::digest(bytes).into(),
    };
    SourceAttachment {
        key: key.clone(),
        source_directory: identity(0),
        holder_directory: identity(1),
        holder_name: data.holder_leaf().as_bytes().to_vec(),
        original_record: record(2, data.original_record()),
        withheld_record: record(3, data.withheld_record()),
    }
}

fn scope_current(state: &State) -> io::Result<()> {
    if let Some(source) = &state.preparation_source {
        source.check_current()?;
    }
    if let Some(inputs) = &state.preparation_inputs {
        inputs.check_current()?;
    }
    if let Some(owners) = &state.dependency_owners {
        owners.check()?;
    }
    if let Some(source) = &state.source {
        source.check_current()?;
    }
    if let Some(offer) = &state.source_offer {
        offer.check_current()?;
    }
    if let Some(scope) = &state.scope {
        scope.upgrade()?.check_current()?;
    }
    Ok(())
}

fn witnesses(server: &Jobserver) -> io::Result<([OwnedFd; 2], GnuIdentity)> {
    let (read, write, path) = match server.client().transport_witnesses()? {
        jobserver::TransportWitnesses::NumericPipe { read, write } => (read, write, None),
        jobserver::TransportWitnesses::NamedFifo { read, write, path } => (read, write, Some(path)),
    };
    let identity = |fd: &OwnedFd| -> io::Result<FileIdentity> {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let stat = unsafe { stat.assume_init() };
        Ok(FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino })
    };
    let a = identity(&read)?;
    let b = identity(&write)?;
    let gnu = match path {
        Some(path) if a == b => {
            GnuIdentity::NamedFifo { path: path.as_os_str().as_bytes().to_vec(), backing: a }
        }
        Some(_) => return Err(io::Error::other("original named GNU witnesses differ")),
        None => GnuIdentity::NumericPipe { read: a, write: b },
    };
    let descriptions = [read, write];
    trust_resource_controller::bootstrap_graph::transport::check_gnu_identity(
        &gnu,
        &descriptions.each_ref().map(AsFd::as_fd),
    )?;
    Ok((descriptions, gnu))
}
fn fd_identity(fd: std::os::fd::BorrowedFd<'_>) -> io::Result<FileIdentity> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: read-only observation of the actual borrowed original; no flag,
    // cursor, lock state or descriptor ownership changes.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let stat = unsafe { stat.assume_init() };
    Ok(FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino })
}
fn gnu_check(server: &Jobserver, expected: &GnuIdentity) -> io::Result<()> {
    let (_, actual) = witnesses(server)?;
    if &actual != expected {
        return Err(io::Error::other("original GNU transport changed"));
    }
    Ok(())
}
fn stamp(meta: &std::fs::Metadata) -> (u64, u64, u64, i64, i64, i64, i64) {
    (
        meta.dev(),
        meta.ino(),
        meta.len(),
        meta.mtime(),
        meta.mtime_nsec(),
        meta.ctime(),
        meta.ctime_nsec(),
    )
}
fn image(path: &std::path::Path, deadline: Instant) -> io::Result<MetadataFile> {
    time(deadline)?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
        .open(path)?;
    let before = file.metadata()?;
    if !before.is_file()
        || before.nlink() != 1
        || before.uid() != unsafe { libc::geteuid() }
        || before.len() == 0
        || before.len() > 1024 * 1024 * 1024
    {
        return Err(io::Error::other("native SDK query image refused"));
    }
    let mut hash = Sha256::new();
    let mut offset = 0;
    let mut buffer = [0; 64 * 1024];
    loop {
        time(deadline)?;
        let count = file.read_at(&mut buffer, offset)?;
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
        offset += count as u64;
    }
    if offset != before.len()
        || stamp(&before) != stamp(&file.metadata()?)
        || stamp(&before) != stamp(&std::fs::symlink_metadata(path)?)
    {
        return Err(io::Error::other("native SDK query image changed"));
    }
    time(deadline)?;
    Ok(MetadataFile {
        path: path.as_os_str().as_bytes().to_vec(),
        sha256: hash.finalize().into(),
        bytes: before.len(),
        device: before.dev(),
        inode: before.ino(),
    })
}
#[derive(Debug)]
struct PreparationError {
    stage: &'static str,
    observation: Option<String>,
    original: io::Error,
}
impl std::fmt::Display for PreparationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native SDK query {}", self.stage)?;
        if let Some(observation) = &self.observation {
            write!(f, " ({observation})")?;
        }
        write!(f, ": {}", self.original)
    }
}
impl std::error::Error for PreparationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.original)
    }
}
fn preparation_error(
    stage: &'static str,
    observation: Option<String>,
    original: io::Error,
) -> io::Error {
    io::Error::new(original.kind(), PreparationError { stage, observation, original })
}

// Descriptive DATA only, evaluated only AFTER the same strict validator has
// refused. No environment values, original keys/nonces, paths or hashes enter
// the diagnostic. These partial observations are never an alternate validator.
fn validate_request(request: &query::Request) -> io::Result<()> {
    request.validate().map_err(|error| {
        let names = request
            .environment
            .iter()
            .take(16)
            .map(|(key, _)| {
                let mut name = key[..key.len().min(64)].escape_ascii().to_string();
                if key.len() > 64 {
                    name.push_str("...");
                }
                name
            })
            .collect::<Vec<_>>();
        let program_suffix = match request.tool {
            query::Tool::Compiler => b"/bin/trustc".as_slice(),
            query::Tool::Targo => b"/bin/targo".as_slice(),
            query::Tool::Formatter => b"/bin/trustfmt".as_slice(),
            query::Tool::DependencyPlanner => b"/bin/python3.14".as_slice(),
        };
        let observation = format!(
            "key_binding_valid={}, gnu={}, tool={:?}, program_binding_matches={}, program_bytes={}, program_inode_present={}, sdk_root_absolute={}, cwd_absolute={}, argv_count={}, environment_count={}, environment_key_prefix={names:?}, timeout_ns={}",
            request.key.validate().is_ok(),
            match &request.gnu {
                GnuIdentity::NumericPipe { .. } => "numeric-pipe",
                GnuIdentity::NamedFifo { .. } => "named-fifo",
            },
            request.tool,
            request.program.path.strip_prefix(request.sdk_root.as_slice()) == Some(program_suffix),
            request.program.bytes,
            request.program.inode != 0,
            request.sdk_root.starts_with(b"/"),
            request.cwd.starts_with(b"/"),
            request.arguments.len(),
            request.environment.len(),
            request.timeout_ns,
        );
        preparation_error("request validation", Some(observation), error)
    })
}

fn request(
    command: &Command,
    context: &ContextReply,
    key: &Key,
    sequence: u64,
    gnu: GnuIdentity,
    deadline: Instant,
) -> io::Result<query::Request> {
    let program = std::path::Path::new(command.get_program());
    let sdk =
        context.context.sdk.as_ref().ok_or_else(|| io::Error::other("original SDK unavailable"))?;
    let (root, tool) = sdk_program(&sdk.execution, program)?;
    let mut environment = std::env::vars_os().collect::<BTreeMap<_, _>>();
    for (key, value) in command.get_envs() {
        match value {
            Some(value) => {
                environment.insert(key.to_owned(), value.to_owned());
            }
            None => {
                environment.remove(key);
            }
        }
    }
    // Exclude only the private original transport whose real owners this
    // bridge retains. All remaining effective values enter the closed profile;
    // no config, loader, policy or ordinary value is silently stripped.
    for key in [
        "MAKEFLAGS",
        "MFLAGS",
        "CARGO_MAKEFLAGS",
        jobserver_utils::DESCENDANT_HANDOFF_ENV,
        trust_resource_controller::client::sdk::SDK_LEASE_ENV,
        trust_resource_controller::bootstrap_graph::HOST_STORE_FD_ENV,
        "ATERM_RESOURCE_JOB_V3",
    ] {
        environment.remove(std::ffi::OsStr::new(key));
    }
    let mut operation = [0; 16];
    use std::io::Read as _;
    let mut random = File::open("/dev/urandom")?;
    let key = key.clone();
    while operation == [0; 16]
        || operation == key.graph
        || operation == key.query.call_attempt
        || operation == key.query.binding.root_attempt
    {
        time(deadline)?;
        random.read_exact(&mut operation)?;
    }
    let cwd = command
        .get_current_dir()
        .map(std::path::Path::to_owned)
        .map(Ok)
        .unwrap_or_else(std::env::current_dir)?;
    let remaining = deadline
        .saturating_duration_since(Instant::now())
        .as_nanos()
        .min(u128::from(query::MAX_QUERY_NS));
    let request = query::Request {
        key: query::OperationKey { graph: key, sequence, operation },
        gnu,
        tool,
        sdk_root: root.as_os_str().as_bytes().to_vec(),
        program: image(program, deadline)?,
        cwd: cwd.as_os_str().as_bytes().to_vec(),
        arguments: command.get_args().map(|arg| arg.as_bytes().to_vec()).collect(),
        environment: environment
            .into_iter()
            .map(|(key, value)| (key.as_bytes().to_vec(), value.as_bytes().to_vec()))
            .collect(),
        timeout_ns: remaining as u64,
    };
    validate_request(&request)?;
    time(deadline)?;
    Ok(request)
}

fn sdk_program(
    execution: &[u8],
    program: &std::path::Path,
) -> io::Result<(std::path::PathBuf, query::Tool)> {
    // The original Keeper observes its SDK root in SdkCustody.execution.
    // Program selection remains exact and gains no authority from this path.
    let root = std::path::PathBuf::from(std::ffi::OsStr::from_bytes(execution));
    if !root.is_absolute() {
        return Err(io::Error::other("original SDK execution root is not absolute"));
    }
    let tool = if program == root.join("bin/trustc") {
        query::Tool::Compiler
    } else if program == root.join("bin/targo") {
        query::Tool::Targo
    } else {
        return Err(io::Error::other(
            "Bootstrap command has no qualified original SDK input/profile",
        ));
    };
    Ok((root, tool))
}
fn observed_status(status: &Status) -> io::Result<ExitStatus> {
    use std::os::unix::process::ExitStatusExt as _;
    match status {
        Status::Finished { outcome: Outcome::Exit(code), .. } if (0..=255).contains(code) => {
            Ok(ExitStatus::from_raw(code << 8))
        }
        Status::Finished { outcome: Outcome::Signal(signal), .. } if (1..=31).contains(signal) => {
            Ok(ExitStatus::from_raw(*signal))
        }
        _ => Err(io::Error::other("native SDK query has no representable actual outcome")),
    }
}

#[cfg(test)]
#[path = "host_graph/tests.rs"]
mod tests;
