//! One actual Rust source task before the Host object operation. Its opaque
//! predecessor retains the original capture; observations cannot construct it.

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

use build_helper::trust_repo_lock::management::{ScopeDispatch, ScopeIdentity, WeakScopeDispatch};

use super::*;

pub(super) struct Inputs {
    pub(super) file: File,
    stamp: SourceStamp,
    parents: SourceParents,
    pub(super) source: Arc<OriginalSourceRoot>,
    pub(super) output: Arc<BuildOwnership>,
    pub(super) command: Arc<CommandOwnership>,
    scope: WeakScopeDispatch,
    identity: ScopeIdentity,
    deadline: Instant,
}
impl Inputs {
    fn check(&self, deadline: Instant) -> io::Result<()> {
        if deadline > self.deadline {
            return Err(io::Error::other("cannot extend original source-task deadline"));
        }
        time(deadline)?;
        let scope = self.scope.upgrade()?;
        if scope.identity() != &self.identity {
            return Err(io::Error::other("source task lost its original protected scope"));
        }
        self.source.check_current()?;
        self.output.check().map_err(io::Error::other)?;
        self.parents.check(&self.source, deadline)?;
        if source_stamp(&self.file.metadata()?) != self.stamp
            || named_stamp(self.parents.bootstrap.as_fd(), c"native_object.rs")? != self.stamp
        {
            return Err(io::Error::other("source-task selected original changed"));
        }
        time(deadline)
    }
    fn read(&self, deadline: Instant) -> io::Result<MetadataFile> {
        self.check(deadline)?;
        let meta = self.file.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.mode() & 0o022 != 0
            || meta.len() != object::SOURCE_BYTES.len() as u64
        {
            return Err(io::Error::other("outside the closed native source-task input"));
        }
        let mut bytes = vec![0; object::SOURCE_BYTES.len() + 1];
        let mut offset = 0;
        while offset < bytes.len() {
            time(deadline)?;
            match self.file.read_at(&mut bytes[offset..], offset as u64) {
                Ok(0) => break,
                Ok(count) => offset += count,
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) => return Err(error),
            }
        }
        bytes.truncate(offset);
        let sha256: [u8; 32] = Sha256::digest(&bytes).into();
        if bytes != object::SOURCE_BYTES || sha256 != object::SOURCE_SHA256 {
            return Err(io::Error::other("native source-task bytes differ from NativeLeafV1"));
        }
        self.check(deadline)?;
        Ok(MetadataFile {
            path: self
                .source
                .path()
                .join(std::ffi::OsStr::from_bytes(object::SOURCE_RELATIVE_PATH))
                .as_os_str()
                .as_bytes()
                .to_vec(),
            sha256,
            bytes: offset as u64,
            device: meta.dev(),
            inode: meta.ino(),
        })
    }
}

struct Record {
    inputs: Arc<Inputs>,
    observed: MetadataFile,
    claimed: AtomicBool,
}
enum State {
    Captured,
    Running,
    Complete(Arc<Record>),
    Failed(Arc<Failure>),
}

/// Root retains every attempted source task, including the exact returned
/// observation and all distinct errors when native/closing bookends refuse.
pub(in crate::utils::metadata_scheduler::host_graph) struct Attempt {
    inputs: Arc<Inputs>,
    state: Mutex<State>,
}
struct Failure {
    _inputs: Arc<Inputs>,
    returned: Option<MetadataFile>,
    work: Option<io::Error>,
    native: Option<io::Error>,
    inner_bookend: Option<io::Error>,
    outer_bookend: Option<io::Error>,
    census: Option<io::Error>,
}
struct SourceError(Arc<Failure>);
fn failure_error(failure: Arc<Failure>) -> io::Error {
    let kind = failure
        .work
        .as_ref()
        .or(failure.native.as_ref())
        .or(failure.inner_bookend.as_ref())
        .or(failure.outer_bookend.as_ref())
        .or(failure.census.as_ref())
        .map_or(io::ErrorKind::Other, io::Error::kind);
    io::Error::new(kind, SourceError(failure))
}
impl std::fmt::Debug for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SourceTaskFailure")
            .field("returned", &self.0.returned)
            .field("work", &self.0.work)
            .field("native", &self.0.native)
            .field("inner_bookend", &self.0.inner_bookend)
            .field("outer_bookend", &self.0.outer_bookend)
            .field("census", &self.0.census)
            .finish()
    }
}
impl std::fmt::Display for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "original source task refused")?;
        for (stage, error) in [
            ("work", &self.0.work),
            ("native join", &self.0.native),
            ("worker bookend", &self.0.inner_bookend),
            ("caller bookend", &self.0.outer_bookend),
            ("census", &self.0.census),
        ] {
            if let Some(error) = error {
                write!(f, "; {stage}: {error}")?;
            }
        }
        Ok(())
    }
}
impl std::error::Error for SourceError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.0
            .work
            .as_ref()
            .or(self.0.native.as_ref())
            .or(self.0.inner_bookend.as_ref())
            .or(self.0.outer_bookend.as_ref())
            .or(self.0.census.as_ref())
            .map(|error| error as _)
    }
}

/// Only an actual joined source task and all original bookends mint this.
/// Non-Clone; it cannot be reconstructed from MetadataFile or a task index.
pub(super) struct Predecessor(Arc<Record>);
pub(super) struct BoundSource(Arc<Record>);

impl Attempt {
    pub(super) fn capture(
        source: Arc<OriginalSourceRoot>,
        output: Arc<BuildOwnership>,
        command: Arc<CommandOwnership>,
        scope: ScopeDispatch,
        deadline: Instant,
    ) -> io::Result<Arc<Self>> {
        let deadline = deadline.min(scope.deadline());
        time(deadline)?;
        scope.check_current()?;
        let (file, parents) = open_source(&source, deadline)?;
        let stamp = source_stamp(&file.metadata()?);
        let inputs = Arc::new(Inputs {
            file,
            stamp,
            parents,
            source,
            output,
            command,
            scope: scope.downgrade(),
            identity: scope.identity().clone(),
            deadline,
        });
        inputs.check(deadline)?;
        Ok(Arc::new(Self { inputs, state: Mutex::new(State::Captured) }))
    }
    pub(super) fn run(&self) -> io::Result<Predecessor> {
        self.run_with(|input, deadline| input.read(deadline))
    }
    fn run_with(
        &self,
        work: impl FnOnce(&Inputs, Instant) -> io::Result<MetadataFile> + Send,
    ) -> io::Result<Predecessor> {
        {
            let mut state =
                self.state.lock().map_err(|_| io::Error::other("source task poisoned"))?;
            if !matches!(*state, State::Captured) {
                return Err(io::Error::other("source task cannot run twice or replay an unknown"));
            }
            *state = State::Running;
        }
        let mut returned = None;
        let mut work_error = None;
        let mut inner_bookend = None;
        let deadline = self.inputs.deadline;
        // The callback writes its result to the caller-owned slot before the
        // worker and scheduler's closing checks. A denied join loses no output.
        let native = crate::utils::metadata_scheduler::run_native_worker(
            &self.inputs.identity,
            deadline,
            |effective| {
                match self.inputs.check(effective).and_then(|()| work(&self.inputs, effective)) {
                    Ok(value) => returned = Some(value),
                    Err(error) => work_error = Some(error),
                }
                inner_bookend = self.inputs.check(effective).err();
            },
        );
        let outer_bookend = self.inputs.check(deadline).err();
        // Poison is refusal only. Preserve actual callback output and inputs
        // in Failed, without manufacturing a completed predecessor.
        let (mut state, census) = match self.state.lock() {
            Ok(state) => (state, None),
            Err(poisoned) => (
                poisoned.into_inner(),
                Some(io::Error::other("source-task census poisoned after work")),
            ),
        };
        if work_error.is_some()
            || native.is_err()
            || inner_bookend.is_some()
            || outer_bookend.is_some()
            || census.is_some()
            || returned.is_none()
        {
            let failure = Arc::new(Failure {
                _inputs: Arc::clone(&self.inputs),
                returned,
                work: work_error,
                native: native.err(),
                inner_bookend,
                outer_bookend,
                census,
            });
            *state = State::Failed(Arc::clone(&failure));
            return Err(failure_error(failure));
        }
        let record = Arc::new(Record {
            inputs: Arc::clone(&self.inputs),
            observed: returned.unwrap(),
            claimed: AtomicBool::new(false),
        });
        *state = State::Complete(Arc::clone(&record));
        Ok(Predecessor(record))
    }
}

impl Predecessor {
    pub(super) fn deadline(&self) -> Instant {
        self.0.inputs.deadline
    }
    // Finish only the source-work restriction, under the original graph lock.
    // A concurrently recorded terminal refusal is permanent and cannot be
    // overwritten by this actual successful read/join.
    pub(super) fn finish_activity(
        self,
        active: &mut bool,
        terminal_failed: bool,
    ) -> io::Result<Self> {
        if !*active || terminal_failed {
            return Err(io::Error::other("original source graph has a terminal refusal"));
        }
        self.0.inputs.check(self.deadline())?;
        *active = false;
        Ok(self)
    }
    pub(super) fn bind(
        self,
        attempts: &[Arc<Attempt>],
        source: &Arc<OriginalSourceRoot>,
        output: &Arc<BuildOwnership>,
        command: &Arc<CommandOwnership>,
    ) -> io::Result<BoundSource> {
        let mut found = false;
        for attempt in attempts {
            let state =
                attempt.state.lock().map_err(|_| io::Error::other("source task poisoned"))?;
            match &*state {
                State::Complete(record) => found |= Arc::ptr_eq(record, &self.0),
                State::Failed(failure) => {
                    return Err(failure_error(Arc::clone(failure)));
                }
                State::Captured | State::Running => {
                    return Err(io::Error::other("source-task census remains unresolved"));
                }
            }
        }
        if !found
            || !Arc::ptr_eq(source, &self.0.inputs.source)
            || !Arc::ptr_eq(output, &self.0.inputs.output)
            || !Arc::ptr_eq(command, &self.0.inputs.command)
        {
            return Err(io::Error::other(
                "object predecessor is not this same original source task",
            ));
        }
        self.0.inputs.check(self.deadline())?;
        if self
            .0
            .claimed
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Err(io::Error::other("source predecessor was already consumed"));
        }
        Ok(BoundSource(self.0))
    }
}
impl BoundSource {
    pub(super) fn inputs(&self) -> &Inputs {
        &self.0.inputs
    }
    pub(super) fn observation(&self) -> &MetadataFile {
        &self.0.observed
    }
    pub(super) fn check(&self, deadline: Instant) -> io::Result<()> {
        self.0.inputs.check(deadline)
    }
    pub(super) fn exclude_output(
        &self,
        output: trust_resource_controller::FileIdentity,
    ) -> io::Result<()> {
        self.0.inputs.parents.exclude_output(output)
    }
}

#[cfg(test)]
mod tests;
