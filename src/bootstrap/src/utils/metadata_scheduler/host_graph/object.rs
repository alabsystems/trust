//! Actual source/output-owner connection for one closed producing node.
use std::ffi::CString;
use std::fs::File;
use std::io;
use std::os::fd::{AsFd as _, AsRawFd as _, FromRawFd as _};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{FileExt as _, MetadataExt as _};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use build_helper::trust_repo_lock::management::OriginalSourceRoot;
use sha2::{Digest as _, Sha256};
use trust_resource_controller::bootstrap_graph::{object, query};
use trust_resource_controller::client::bootstrap_graph::CompletedObjectCompile;
use trust_resource_controller::{MetadataFile, Outcome, Status};

use super::{
    OriginalHostGraph, Phase, State, fd_identity, image, lock, scope_current, time, witnesses,
};
use crate::core::build_steps::frontend_runtime::{BuildOwnership, CommandOwnership};

pub(super) mod source_task;

/// Diagnostic observations; construction of the actual owner remains private.
#[derive(Clone, Debug)]
pub(crate) struct NativeObjectObservation {
    pub(crate) path: PathBuf,
    pub(crate) sha256: [u8; 32],
    pub(crate) bytes: u64,
    pub(crate) source: MetadataFile,
}
pub(super) struct OriginalObject {
    // Actual joined source predecessor, retaining the SAME selected File and
    // original parent/source/output/command owners before any RPC is exposed.
    source_task: source_task::BoundSource,
    request: object::Request,
    deadline: Instant,
    completed: Option<CompletedObjectCompile>,
    artifact: Option<File>,
}
impl OriginalObject {
    fn check(&self, deadline: Instant) -> io::Result<()> {
        if deadline > self.deadline {
            return Err(io::Error::other("cannot extend original object operation deadline"));
        }
        time(deadline)?;
        self.source_task.check(deadline)?;
        let original = self.source_task.inputs();
        object::transport::check_source(
            &self.request,
            &[original.source.directory()?, original.file.as_fd()],
            deadline,
        )?;
        // SAFETY: these are SAME typed graph originals, not a reopened guard.
        let descriptions = unsafe {
            original.output.original_output(
                &original.command,
                Path::new(std::ffi::OsStr::from_bytes(&self.request.output_root)),
            )
        }
        .map_err(io::Error::other)?;
        if fd_identity(descriptions.directory())? != self.request.output_directory
            || fd_identity(descriptions.lock())? != self.request.output_lock
        {
            return Err(io::Error::other("original object output descriptions changed"));
        }
        time(deadline)
    }
}

type SourceStamp = (u64, u64, u64, u32, u32, u32, u64, i64, i64, i64, i64);
fn source_stamp(meta: &std::fs::Metadata) -> SourceStamp {
    (
        meta.dev(),
        meta.ino(),
        meta.len(),
        meta.mode(),
        meta.uid(),
        meta.gid(),
        meta.nlink(),
        meta.mtime(),
        meta.mtime_nsec(),
        meta.ctime(),
        meta.ctime_nsec(),
    )
}

// Select one restriction before input work; neither later work nor a root's
// longer lifetime can reset/extend this operation's original delivery bound.
fn operation_deadline(original_root: Instant, started: Instant) -> io::Result<Instant> {
    let limit = started
        .checked_add(std::time::Duration::from_nanos(object::MAX_COMPILE_NS))
        .ok_or_else(|| io::Error::other("native object deadline is unrepresentable"))?;
    let deadline = original_root.min(limit);
    time(deadline)?;
    Ok(deadline)
}

struct SourceParents {
    root: SourceStamp,
    src: File,
    src_stamp: SourceStamp,
    bootstrap: File,
    bootstrap_stamp: SourceStamp,
}
fn native_stamp(meta: libc::stat) -> SourceStamp {
    (
        meta.st_dev as u64,
        meta.st_ino,
        meta.st_size as u64,
        meta.st_mode as u32,
        meta.st_uid,
        meta.st_gid,
        meta.st_nlink as u64,
        meta.st_mtime,
        meta.st_mtime_nsec,
        meta.st_ctime,
        meta.st_ctime_nsec,
    )
}
fn fd_stamp(fd: std::os::fd::BorrowedFd<'_>) -> io::Result<SourceStamp> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(native_stamp(unsafe { stat.assume_init() }))
}
fn named_stamp(
    parent: std::os::fd::BorrowedFd<'_>,
    name: &std::ffi::CStr,
) -> io::Result<SourceStamp> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe {
        libc::fstatat(
            parent.as_raw_fd(),
            name.as_ptr(),
            stat.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(native_stamp(unsafe { stat.assume_init() }))
}
impl SourceParents {
    fn check(&self, root: &OriginalSourceRoot, deadline: Instant) -> io::Result<()> {
        time(deadline)?;
        root.check_current()?;
        let original = root.directory()?;
        if fd_stamp(original)? != self.root
            || source_stamp(&self.src.metadata()?) != self.src_stamp
            || source_stamp(&self.bootstrap.metadata()?) != self.bootstrap_stamp
            || named_stamp(original, c"src")? != self.src_stamp
            || named_stamp(self.src.as_fd(), c"bootstrap")? != self.bootstrap_stamp
        {
            return Err(io::Error::other("original source parent namespace changed since capture"));
        }
        time(deadline)
    }
    fn exclude_output(&self, output: trust_resource_controller::FileIdentity) -> io::Result<()> {
        if [&self.root, &self.src_stamp, &self.bootstrap_stamp]
            .iter()
            .any(|stamp| (stamp.0, stamp.1) == (output.device, output.inode))
        {
            return Err(io::Error::other("object output cannot mutate an original source parent"));
        }
        Ok(())
    }
}

fn open_source(root: &OriginalSourceRoot, deadline: Instant) -> io::Result<(File, SourceParents)> {
    time(deadline)?;
    root.check_current()?;
    let original = fd_stamp(root.directory()?)?;
    let mut directories = Vec::<File>::new();
    for (index, name) in [c"src", c"bootstrap", c"native_object.rs"].iter().enumerate() {
        let parent =
            directories.last().map_or(root.directory()?.as_raw_fd(), |file| file.as_raw_fd());
        let flags = libc::O_RDONLY
            | libc::O_CLOEXEC
            | libc::O_NOFOLLOW
            | libc::O_NONBLOCK
            | if index < 2 { libc::O_DIRECTORY } else { 0 };
        // SAFETY: one fixed component beneath the actual original source root.
        let raw = unsafe { libc::openat(parent, name.as_ptr(), flags) };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        let file = unsafe { File::from_raw_fd(raw) };
        if index == 2 {
            let mut entries = directories.into_iter();
            let src = entries.next().expect("opened actual src directory");
            let bootstrap = entries.next().expect("opened actual bootstrap directory");
            let parents = SourceParents {
                root: original,
                src_stamp: source_stamp(&src.metadata()?),
                bootstrap_stamp: source_stamp(&bootstrap.metadata()?),
                src,
                bootstrap,
            };
            parents.check(root, deadline)?;
            if named_stamp(parents.bootstrap.as_fd(), c"native_object.rs")?
                != source_stamp(&file.metadata()?)
            {
                return Err(io::Error::other(
                    "original source leaf changed while capturing its parents",
                ));
            }
            time(deadline)?;
            return Ok((file, parents));
        }
        directories.push(file);
    }
    unreachable!()
}
fn nonce(
    key: &trust_resource_controller::bootstrap_graph::Key,
    deadline: Instant,
) -> io::Result<[u8; 16]> {
    use std::io::Read as _;
    let mut random = File::open("/dev/urandom")?;
    let mut nonce = [0; 16];
    while nonce == [0; 16]
        || nonce == key.graph
        || nonce == key.query.call_attempt
        || nonce == key.query.binding.root_attempt
    {
        time(deadline)?;
        random.read_exact(&mut nonce)?;
    }
    Ok(nonce)
}

fn inspect_artifact(
    entry: &OriginalObject,
    deadline: Instant,
) -> io::Result<(File, NativeObjectObservation)> {
    entry.check(deadline)?;
    let completed = entry
        .completed
        .as_ref()
        .ok_or_else(|| io::Error::other("same native object completion absent"))?;
    completed.revalidate(deadline)?;
    let actual = completed.observation();
    if !matches!(
        actual.completion.finished.status,
        Status::Finished { outcome: Outcome::Exit(0), .. }
    ) || actual.completion.inputs_unchanged.is_err()
    {
        return Err(io::Error::other(format!(
            "actual native object compiler failed: {:?}",
            actual.completion.finished.status
        )));
    }
    let expected =
        actual.artifact.as_ref().ok_or_else(|| io::Error::other("actual object output absent"))?;
    let input = entry.source_task.inputs();
    // SAFETY: same original close-only acquired guard, retained in entry.
    let descriptions = unsafe {
        input.output.original_output(
            &input.command,
            Path::new(std::ffi::OsStr::from_bytes(&entry.request.output_root)),
        )
    }
    .map_err(io::Error::other)?;
    let name = CString::new(entry.request.destination.clone())
        .map_err(|_| io::Error::other("object leaf contains NUL"))?;
    let raw = unsafe {
        libc::openat(
            descriptions.directory().as_raw_fd(),
            name.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    let file = unsafe { File::from_raw_fd(raw) };
    completed.require_sealed_artifact(&file, deadline)?;
    let before = file.metadata()?;
    if !before.is_file()
        || before.nlink() != 1
        || before.mode() & 0o7777 != 0o400
        || before.uid() != unsafe { libc::geteuid() }
        || before.dev() != expected.device
        || before.ino() != expected.inode
        || before.len() != expected.bytes
        || !(32..=object::MAX_OBJECT_BYTES).contains(&before.len())
    {
        return Err(io::Error::other("published object is not the same sealed original output"));
    }
    let mut header = [0u8; 32];
    file.read_exact_at(&mut header, 0)?;
    // This initial object operation is a native ARM64 Mach-O object, matching
    // the exact qualified existing image; it is not cross-target coverage.
    let word = |index: usize| u32::from_le_bytes(header[index..index + 4].try_into().unwrap());
    if word(0) != 0xfeedfacf
        || word(4) != 0x0100000c
        || word(12) != 1
        || u64::from(word(20)).checked_add(32).is_none_or(|size| size > before.len())
    {
        return Err(io::Error::other("published output is not a bounded native MH_OBJECT"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0; 65536];
    let mut offset = 0;
    while offset < before.len() {
        time(deadline)?;
        let limit = (before.len() - offset).min(buffer.len() as u64) as usize;
        let count = match file.read_at(&mut buffer[..limit], offset) {
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            result => result?,
        };
        if count == 0 {
            return Err(io::Error::other("original object truncated"));
        }
        hash.update(&buffer[..count]);
        offset += count as u64;
    }
    let sha256: [u8; 32] = hash.finalize().into();
    let after = file.metadata()?;
    let mut named = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe {
        libc::fstatat(
            descriptions.directory().as_raw_fd(),
            name.as_ptr(),
            named.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    let named = unsafe { named.assume_init() };
    if sha256 != expected.sha256
        || super::stamp(&before) != super::stamp(&after)
        || after.mode() != before.mode()
        || after.nlink() != before.nlink()
        || named.st_mode & libc::S_IFMT != libc::S_IFREG
        || named.st_dev as u64 != expected.device
        || named.st_ino != expected.inode
    {
        return Err(io::Error::other("original object bytes/name changed"));
    }
    entry.check(deadline)?;
    completed.require_sealed_artifact(&file, deadline)?;
    time(deadline)?;
    Ok((
        file,
        NativeObjectObservation {
            path: PathBuf::from(std::ffi::OsStr::from_bytes(&expected.path)),
            sha256,
            bytes: before.len(),
            source: entry.source_task.observation().clone(),
        },
    ))
}

impl OriginalHostGraph {
    fn prepare_source_task(&self, deadline: Instant) -> io::Result<source_task::Predecessor> {
        let attempt =
            {
                let mut scheduler = lock(&super::super::selected()?.state, deadline)?;
                let mut state = lock(&self.state, deadline)?;
                if scheduler.producer_failed
                    || !scheduler.embedded_original
                    || state.failed
                    || state.source_task_active
                {
                    return Err(io::Error::other("native source graph/scheduler is unresolved"));
                }
                scope_current(&state)?;
                if !matches!(state.phase, Some(Phase::OutputBound(_)))
                    || state.source_tasks.len() >= 4096
                {
                    return Err(io::Error::other(
                        "native source needs a bounded actual output-bound graph",
                    ));
                }
                // Restrict graph transitions before capture/work. Do not hold the
                // scheduler mutex across run_native_worker: that worker borrows
                // this SAME original mutex through its actual callback and join.
                state.source_task_active = true;
                let captured =
                    (|| {
                        source_task::Attempt::capture(
                            Arc::clone(
                                state.source.as_ref().ok_or_else(|| {
                                    io::Error::other("original source owner absent")
                                })?,
                            ),
                            Arc::clone(
                                state.output_owner.as_ref().ok_or_else(|| {
                                    io::Error::other("original output owner absent")
                                })?,
                            ),
                            Arc::clone(state.command_owner.as_ref().ok_or_else(|| {
                                io::Error::other("original command owner absent")
                            })?),
                            state
                                .scope
                                .as_ref()
                                .ok_or_else(|| io::Error::other("original scope absent"))?
                                .upgrade()?,
                            deadline,
                        )
                    })();
                let attempt = match captured {
                    Ok(attempt) => attempt,
                    Err(error) => {
                        state.failed = true;
                        scheduler.producer_failed = true;
                        return Err(error);
                    }
                };
                // Unknown/panic/late bookends retain this exact attempt and every
                // selected input before any actual worker is registered.
                state.source_tasks.push(Arc::clone(&attempt));
                attempt
            };
        let result = attempt.run();
        let mut scheduler = lock(&super::super::selected()?.state, deadline)?;
        let mut state = lock(&self.state, deadline)?;
        let predecessor = match result {
            Ok(predecessor) => predecessor,
            Err(error) => {
                state.failed = true;
                scheduler.producer_failed = true;
                return Err(error);
            }
        };
        if scheduler.producer_failed || !scheduler.embedded_original {
            return Err(io::Error::other("original scheduler did not close its source task"));
        }
        scope_current(&state)?;
        time(deadline)?;
        // Concurrent terminal refusals are never cleared by a successful local
        // worker. Only its distinct in-progress restriction may finish here.
        let failed = state.failed;
        predecessor.finish_activity(&mut state.source_task_active, failed).inspect_err(|_| {
            state.failed = true;
            scheduler.producer_failed = true;
        })
    }

    fn produce_object(
        &self,
        destination: &[u8],
        predecessor: source_task::Predecessor,
    ) -> io::Result<NativeObjectObservation> {
        // Source work is inside this SAME bound; a later object cannot reset
        // the node's deadline after consuming its predecessor.
        let deadline = predecessor.deadline();
        let mut scheduler = lock(&super::super::selected()?.state, deadline)?;
        let mut state = lock(&self.state, deadline)?;
        if scheduler.producer_failed
            || !scheduler.embedded_original
            || state.failed
            || state.source_task_active
        {
            return Err(io::Error::other("native object graph/scheduler is unresolved"));
        }
        scope_current(&state)?;
        if !matches!(state.phase, Some(Phase::OutputBound(_))) {
            return Err(io::Error::other("native object requires actual output-bound graph"));
        }
        state.failed = true;
        scheduler.producer_failed = true;
        if state.objects.len() >= 4096 {
            return Err(io::Error::other("complete object census exceeds bound"));
        }
        let source = Arc::clone(
            state
                .source
                .as_ref()
                .ok_or_else(|| io::Error::other("original source owner absent"))?,
        );
        let output = Arc::clone(
            state
                .output_owner
                .as_ref()
                .ok_or_else(|| io::Error::other("original output owner absent"))?,
        );
        let command = Arc::clone(
            state
                .command_owner
                .as_ref()
                .ok_or_else(|| io::Error::other("original command owner absent"))?,
        );
        source.check_current()?;
        output.check().map_err(io::Error::other)?;
        let source_task = predecessor.bind(&state.source_tasks, &source, &output, &command)?;
        let (gnu_fds, gnu) = witnesses(
            scheduler
                .server
                .as_ref()
                .ok_or_else(|| io::Error::other("same original GNU missing"))?,
        )?;
        let sdk = self
            .context
            .context
            .sdk
            .as_ref()
            .ok_or_else(|| io::Error::other("same original SDK missing"))?;
        let sdk_root = Path::new(std::ffi::OsStr::from_bytes(&sdk.execution));
        let Phase::OutputBound(original) = state.phase.as_ref().unwrap() else { unreachable!() };
        let output_root = Path::new(std::ffi::OsStr::from_bytes(&original.enrollment().output));
        let descriptions =
            unsafe { output.original_output(&command, output_root) }.map_err(io::Error::other)?;
        let request = object::Request {
            key: query::OperationKey {
                graph: self.key.clone(),
                sequence: state.sequence,
                operation: nonce(&self.key, deadline)?,
            },
            gnu,
            sdk_root: sdk.execution.clone(),
            driver: image(&sdk_root.join("bin/tippy-driver"), deadline)?,
            compiler: image(&sdk_root.join("bin/trustc"), deadline)?,
            source_kind: object::SourceKind::NativeLeafV1,
            source_root: source.path().as_os_str().as_bytes().to_vec(),
            source_directory: fd_identity(source.directory()?)?,
            source: source_task.observation().clone(),
            output_root: output_root.as_os_str().as_bytes().to_vec(),
            output_directory: fd_identity(descriptions.directory())?,
            output_lock: fd_identity(descriptions.lock())?,
            destination: destination.to_vec(),
            timeout_ns: deadline
                .saturating_duration_since(Instant::now())
                .as_nanos()
                .min(u128::from(object::MAX_COMPILE_NS)) as u64,
        };
        request.validate()?;
        source_task.exclude_output(request.output_directory)?;
        state.objects.push(OriginalObject {
            source_task,
            request,
            deadline,
            completed: None,
            artifact: None,
        });
        let result = {
            let State { client, phase, objects, .. } = &mut *state;
            let entry = objects.last().unwrap();
            entry.check(deadline)?;
            let input = entry.source_task.inputs();
            let Some(Phase::OutputBound(original)) = phase else { unreachable!() };
            // SAFETY: entry retains SAME typed source/output/command originals
            // before this connect and is retained in graph on every failure.
            unsafe {
                original.compile_object(
                    client,
                    entry.request.clone(),
                    &gnu_fds.each_ref().map(|fd| fd.as_fd()),
                    &[input.source.directory()?, input.file.as_fd()],
                    deadline,
                )
            }
        };
        let completed = match result {
            Ok(value) => value,
            Err(failure) => {
                let error =
                    io::Error::other(format!("original object operation failed: {failure}"));
                state.object_failure = Some(failure);
                return Err(error);
            }
        };
        state.objects.last_mut().unwrap().completed = Some(completed);
        let (file, observation) = inspect_artifact(state.objects.last().unwrap(), deadline)?;
        state.objects.last_mut().unwrap().artifact = Some(file);
        scope_current(&state)?;
        time(deadline)?;
        state.sequence = state
            .sequence
            .checked_add(1)
            .ok_or_else(|| io::Error::other("native object sequence exhausted"))?;
        state.failed = false;
        scheduler.producer_failed = false;
        Ok(observation)
    }
}

impl OriginalHostGraph {
    pub(crate) fn run_native_object_node(&self) -> io::Result<NativeObjectObservation> {
        self.run_object_node(b"trust_bootstrap_native_object.o")
    }
    fn run_object_node(&self, destination: &[u8]) -> io::Result<NativeObjectObservation> {
        let deadline = operation_deadline(self.deadline, Instant::now())?;
        let predecessor = self.prepare_source_task(deadline)?;
        self.produce_object(destination, predecessor)
    }
    /// Reobserve the one actual first-node completion and retained original
    /// artifact. This returns DATA only, never a completed runtime, graph close
    /// or SDK/release owner. Missing/unknown/extra nodes refuse.
    pub fn native_object_result(&self) -> io::Result<MetadataFile> {
        self.check()?;
        let scheduler = lock(&super::super::selected()?.state, self.deadline)?;
        let state = lock(&self.state, self.deadline)?;
        if scheduler.producer_failed
            || !scheduler.embedded_original
            || state.failed
            || state.source_task_active
            || state.source_tasks.len() != 1
            || state.objects.len() != 1
            || state.object_failure.is_some()
            || state.failure.is_some()
            || state.graph_failure.is_some()
            || !matches!(state.phase, Some(Phase::OutputBound(_)))
        {
            return Err(io::Error::other("original native object census is missing or unresolved"));
        }
        let original = &state.objects[0];
        if original.artifact.is_none()
            || original.request.destination != b"trust_bootstrap_native_object.o"
        {
            return Err(io::Error::other("same first-node artifact owner is absent"));
        }
        let deadline = original.deadline.min(self.deadline);
        let (file, observation) = inspect_artifact(original, deadline)?;
        let held = original.artifact.as_ref().expect("same original artifact").metadata()?;
        let named = file.metadata()?;
        if super::stamp(&held) != super::stamp(&named) {
            return Err(io::Error::other("retained native artifact differs from current original"));
        }
        scope_current(&state)?;
        time(deadline)?;
        Ok(MetadataFile {
            path: observation.path.as_os_str().as_bytes().to_vec(),
            sha256: observation.sha256,
            bytes: observation.bytes,
            device: held.dev(),
            inode: held.ino(),
        })
    }
}

pub(crate) fn produce_native_object(destination: &[u8]) -> io::Result<NativeObjectObservation> {
    let graph = super::ORIGINAL
        .get()
        .and_then(std::sync::Weak::upgrade)
        .ok_or_else(|| io::Error::other("actual original Host graph is not installed"))?;
    graph.run_object_node(destination)
}

#[cfg(test)]
mod tests;
