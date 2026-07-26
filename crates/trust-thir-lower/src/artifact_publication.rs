//! Crash-aware publication of a related set of compiler artifacts.
//!
//! A set has one commit marker. Data files are made durable and renamed first;
//! the marker is renamed last. Consumers must treat a missing marker as an
//! incomplete set. Before a new compiler invocation starts semantic work, the
//! previous marker is removed and the directory is synced, then the data files
//! are removed. Consequently an aborted invocation cannot leave the previous
//! generation looking current.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fmt;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use rustc_data_structures::flock::Lock;
use trust_os::{DirFd, FileIdentity, UnixMode};

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
static ACTIVE_PROCESS_DIRECTORIES: OnceLock<Mutex<BTreeSet<ProcessDirectoryKey>>> = OnceLock::new();

/// One immutable artifact in a publication set.
pub(crate) struct Artifact<'a> {
    pub(crate) name: &'a str,
    pub(crate) bytes: &'a [u8],
}

/// A filesystem operation boundary used by deterministic failure-injection
/// tests. The index is the artifact's position: data files first, commit marker
/// last for temporary-file phases.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PublicationPhase {
    ValidatePlan,
    CreateDirectory,
    CanonicalizeDirectory,
    OpenDirectory,
    AcquireTargetLock,
    VerifyTargetLock,
    InvalidateCommitMarker,
    SyncInvalidatedMarkerDirectory,
    InvalidateData(usize),
    InvalidateStaleTemporaries,
    SyncInvalidatedSetDirectory,
    CreateTemporary(usize),
    WriteTemporary(usize),
    SyncTemporary(usize),
    SyncStagedDirectory,
    InstallData(usize),
    SyncInstalledDataDirectory,
    InstallCommitMarker,
    SyncCommittedDirectory,
}

impl fmt::Display for PublicationPhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValidatePlan => f.write_str("validate publication plan"),
            Self::CreateDirectory => f.write_str("create publication directory"),
            Self::CanonicalizeDirectory => f.write_str("canonicalize publication directory"),
            Self::OpenDirectory => f.write_str("open stable publication directory handle"),
            Self::AcquireTargetLock => f.write_str("acquire publication target lock"),
            Self::VerifyTargetLock => f.write_str("verify publication target lock identity"),
            Self::InvalidateCommitMarker => f.write_str("invalidate prior commit marker"),
            Self::SyncInvalidatedMarkerDirectory => {
                f.write_str("sync prior commit-marker invalidation")
            }
            Self::InvalidateData(index) => write!(f, "invalidate prior data artifact {index}"),
            Self::InvalidateStaleTemporaries => f.write_str("invalidate stale temporary artifacts"),
            Self::SyncInvalidatedSetDirectory => f.write_str("sync prior set invalidation"),
            Self::CreateTemporary(index) => write!(f, "create temporary artifact {index}"),
            Self::WriteTemporary(index) => write!(f, "write temporary artifact {index}"),
            Self::SyncTemporary(index) => write!(f, "sync temporary artifact {index}"),
            Self::SyncStagedDirectory => f.write_str("sync staged artifact directory"),
            Self::InstallData(index) => write!(f, "install data artifact {index}"),
            Self::SyncInstalledDataDirectory => f.write_str("sync installed data artifacts"),
            Self::InstallCommitMarker => f.write_str("install commit marker"),
            Self::SyncCommittedDirectory => f.write_str("sync committed artifact set"),
        }
    }
}

/// A publication failure plus any best-effort rollback failures. Rollback
/// failures are never hidden: callers fail compilation on every error.
#[derive(Debug)]
pub(crate) struct PublicationError {
    phase: PublicationPhase,
    source: io::Error,
    rollback_errors: Vec<String>,
}

impl fmt::Display for PublicationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.phase, self.source)?;
        if !self.rollback_errors.is_empty() {
            write!(f, "; rollback failures: {}", self.rollback_errors.join("; "))?;
        }
        Ok(())
    }
}

struct StepError {
    phase: PublicationPhase,
    source: io::Error,
}

trait PhaseHook {
    fn before(&mut self, phase: PublicationPhase) -> io::Result<()>;
}

struct NoopHook;

impl PhaseHook for NoopHook {
    fn before(&mut self, _phase: PublicationPhase) -> io::Result<()> {
        Ok(())
    }
}

#[derive(Debug)]
struct PublicationPlan {
    requested_path: PathBuf,
    directory_path: PathBuf,
    directory: DirFd,
    data_names: Vec<String>,
    commit_name: String,
    lock_name: String,
    temp_prefixes: Vec<String>,
    temp_names: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ProcessDirectoryKey {
    identity: FileIdentity,
}

#[derive(Debug)]
struct ProcessDirectoryLock {
    key: ProcessDirectoryKey,
}

impl ProcessDirectoryLock {
    fn acquire(key: ProcessDirectoryKey, diagnostic_path: &Path) -> io::Result<Self> {
        let mut active = ACTIVE_PROCESS_DIRECTORIES
            .get_or_init(|| Mutex::new(BTreeSet::new()))
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if !active.insert(key.clone()) {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                format!(
                    "publication target is already active in this process: {}",
                    diagnostic_path.display()
                ),
            ));
        }
        Ok(Self { key })
    }
}

impl Drop for ProcessDirectoryLock {
    fn drop(&mut self) {
        let mut active = ACTIVE_PROCESS_DIRECTORIES
            .get_or_init(|| Mutex::new(BTreeSet::new()))
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        active.remove(&self.key);
    }
}

#[derive(Debug)]
struct TargetLock {
    _process: ProcessDirectoryLock,
    _os: Lock,
    directory_identity: FileIdentity,
    identity: FileIdentity,
}

impl TargetLock {
    fn acquire(
        directory: &DirFd,
        requested_path: &Path,
        directory_path: &Path,
        lock_name: &str,
    ) -> io::Result<Self> {
        // The in-process guard closes the fcntl/flock semantic gap on hosts
        // where a second descriptor in one process can share the same lock.
        // It is acquired before opening the sentinel: on process-scoped fcntl
        // hosts, merely closing a second descriptor for that inode can release
        // the first transaction's lock.
        let directory_identity = directory.directory_identity()?;
        // Serialize every publication in one directory inside this process,
        // not only byte-identical lock-name spellings. Case-insensitive and
        // normalization-folding filesystems can map two distinct spellings to
        // the same sentinel inode. On process-scoped `fcntl` hosts, opening and
        // later closing that alias can release the first transaction's lock.
        // There is no race-free way to discover the aliased inode before the
        // protective open, so the stable directory identity is the necessary
        // pre-open exclusion key. Separate compiler processes still retain
        // per-target concurrency through their OS sentinel locks.
        let key = ProcessDirectoryKey { identity: directory_identity };
        let lock_path = directory_path.join(lock_name);
        let process = ProcessDirectoryLock::acquire(key, &lock_path)?;
        // The sentinel inode is permanent. Unlinking it would allow another
        // process to lock a replacement inode while this guard still owns the
        // original one. The OS releases the advisory lock on process death.
        let file = match directory.create_file(lock_name, UnixMode::OWNER_READ_WRITE) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                directory.open_file_read_write(lock_name)?
            }
            Err(error) => return Err(error),
        };
        validate_lock_sentinel(directory, &file, &lock_path)?;
        let identity = directory.file_identity(&file)?;
        file.sync_all()?;
        let os = Lock::from_file(file, true, true)?;
        let lock = Self { _process: process, _os: os, directory_identity, identity };
        lock.verify(directory, requested_path, directory_path, lock_name)?;
        directory.sync_all()?;
        Ok(lock)
    }

    fn verify(
        &self,
        directory: &DirFd,
        requested_path: &Path,
        directory_path: &Path,
        lock_name: &str,
    ) -> io::Result<()> {
        let current_lock = directory.identity(lock_name)?;
        if current_lock != self.identity {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!(
                    "publication lock sentinel changed while locked: {}",
                    directory_path.join(lock_name).display()
                ),
            ));
        }
        let current_path = fs::canonicalize(requested_path)?;
        let current_directory = DirFd::open(&current_path)?;
        let current_identity = current_directory.directory_identity()?;
        if current_identity != self.directory_identity {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!(
                    "requested publication directory changed while locked: {} (initially {})",
                    requested_path.display(),
                    directory_path.display()
                ),
            ));
        }
        Ok(())
    }
}

fn validate_lock_sentinel(directory: &DirFd, file: &File, path: &Path) -> io::Result<()> {
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("publication lock sentinel is not a regular file: {}", path.display()),
        ));
    }
    if directory.file_link_count(file)? != 1 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("publication lock sentinel must have exactly one link: {}", path.display()),
        ));
    }
    Ok(())
}

/// A target whose previous generation has already been invalidated. Prepare
/// this before lowering/validation that can fail, then publish only after all
/// semantic checks and serialization have succeeded.
#[derive(Debug)]
pub(crate) struct PreparedPublication {
    plan: PublicationPlan,
    _target_lock: TargetLock,
}

impl PreparedPublication {
    pub(crate) fn prepare(
        directory: PathBuf,
        data_names: Vec<String>,
        commit_name: String,
    ) -> Result<Self, PublicationError> {
        let mut hook = NoopHook;
        Self::prepare_with_hook(directory, data_names, commit_name, &mut hook)
    }

    fn prepare_with_hook<H: PhaseHook>(
        directory: PathBuf,
        data_names: Vec<String>,
        commit_name: String,
        hook: &mut H,
    ) -> Result<Self, PublicationError> {
        if let Err(source) = validate_plan(&data_names, &commit_name) {
            return Err(PublicationError {
                phase: PublicationPhase::ValidatePlan,
                source,
                rollback_errors: Vec::new(),
            });
        }

        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let temp_names = data_names
            .iter()
            .chain(std::iter::once(&commit_name))
            .map(|name| format!(".{name}.trustc-publish-{}-{sequence}.tmp", std::process::id()))
            .collect::<Vec<_>>();
        let temp_prefixes = data_names
            .iter()
            .chain(std::iter::once(&commit_name))
            .map(|name| format!(".{name}.trustc-publish-"))
            .collect();
        let lock_name = format!(".{commit_name}.trustc-publish.lock");
        if let Err(source) =
            validate_control_names(&data_names, &commit_name, &lock_name, &temp_names)
        {
            return Err(PublicationError {
                phase: PublicationPhase::ValidatePlan,
                source,
                rollback_errors: Vec::new(),
            });
        }

        // Nothing before the advisory lock is acquired mutates a potentially
        // active artifact generation. In particular, an unsupported locking
        // host or a compromised sentinel fails without racing another writer.
        let requested_path = if directory.is_absolute() {
            directory
        } else {
            match std::env::current_dir() {
                Ok(current) => current.join(directory),
                Err(source) => {
                    return Err(PublicationError {
                        phase: PublicationPhase::CanonicalizeDirectory,
                        source,
                        rollback_errors: Vec::new(),
                    });
                }
            }
        };
        let opened: Result<(PathBuf, DirFd, TargetLock), StepError> = (|| {
            step(hook, PublicationPhase::CreateDirectory, || fs::create_dir_all(&requested_path))?;
            let directory_path = step(hook, PublicationPhase::CanonicalizeDirectory, || {
                fs::canonicalize(&requested_path)
            })?;
            let stable_directory =
                step(hook, PublicationPhase::OpenDirectory, || DirFd::open(&directory_path))?;
            let target_lock = step(hook, PublicationPhase::AcquireTargetLock, || {
                TargetLock::acquire(&stable_directory, &requested_path, &directory_path, &lock_name)
            })?;
            Ok((directory_path, stable_directory, target_lock))
        })();
        let (directory_path, stable_directory, target_lock) = match opened {
            Ok(opened) => opened,
            Err(error) => {
                return Err(PublicationError {
                    phase: error.phase,
                    source: error.source,
                    rollback_errors: Vec::new(),
                });
            }
        };
        let plan = PublicationPlan {
            requested_path,
            directory_path,
            directory: stable_directory,
            data_names,
            commit_name,
            lock_name,
            temp_prefixes,
            temp_names,
        };

        let prepared: Result<(), StepError> = (|| {
            locked_step(hook, PublicationPhase::VerifyTargetLock, &plan, &target_lock, || Ok(()))?;
            locked_step(
                hook,
                PublicationPhase::InvalidateCommitMarker,
                &plan,
                &target_lock,
                || remove_file_if_present(&plan.directory, &plan.commit_name),
            )?;
            locked_step(
                hook,
                PublicationPhase::SyncInvalidatedMarkerDirectory,
                &plan,
                &target_lock,
                || plan.directory.sync_all(),
            )?;
            for (index, name) in plan.data_names.iter().enumerate() {
                locked_step(
                    hook,
                    PublicationPhase::InvalidateData(index),
                    &plan,
                    &target_lock,
                    || remove_file_if_present(&plan.directory, name),
                )?;
            }
            locked_step(
                hook,
                PublicationPhase::InvalidateStaleTemporaries,
                &plan,
                &target_lock,
                || remove_stale_temporaries(&plan),
            )?;
            locked_step(
                hook,
                PublicationPhase::SyncInvalidatedSetDirectory,
                &plan,
                &target_lock,
                || plan.directory.sync_all(),
            )?;
            Ok(())
        })();

        match prepared {
            Ok(()) => Ok(Self { plan, _target_lock: target_lock }),
            Err(error) => {
                let rollback_errors = rollback(&plan, &target_lock);
                Err(PublicationError { phase: error.phase, source: error.source, rollback_errors })
            }
        }
    }

    /// Publish exactly the data files supplied to `prepare`, followed by the
    /// commit marker. The marker bytes should bind the data generation (the
    /// direct-TrustIR caller records domain-separated SHA-256 digests).
    pub(crate) fn publish(self, artifacts: &[Artifact<'_>]) -> Result<(), PublicationError> {
        let mut hook = NoopHook;
        self.publish_with_hook(artifacts, &mut hook)
    }

    fn publish_with_hook<H: PhaseHook>(
        self,
        artifacts: &[Artifact<'_>],
        hook: &mut H,
    ) -> Result<(), PublicationError> {
        if let Err(source) = validate_artifacts(&self.plan, artifacts) {
            let rollback_errors = rollback(&self.plan, &self._target_lock);
            return Err(PublicationError {
                phase: PublicationPhase::ValidatePlan,
                source,
                rollback_errors,
            });
        }

        let result: Result<(), StepError> = (|| {
            let mut files = Vec::with_capacity(artifacts.len());
            for (index, name) in self.plan.temp_names.iter().enumerate() {
                let file = locked_step(
                    hook,
                    PublicationPhase::CreateTemporary(index),
                    &self.plan,
                    &self._target_lock,
                    || self.plan.directory.create_file(name, UnixMode::OWNER_READ_WRITE),
                )?;
                files.push(file);
            }
            for (index, (file, artifact)) in files.iter_mut().zip(artifacts).enumerate() {
                locked_step(
                    hook,
                    PublicationPhase::WriteTemporary(index),
                    &self.plan,
                    &self._target_lock,
                    || file.write_all(artifact.bytes),
                )?;
            }
            for (index, file) in files.iter().enumerate() {
                locked_step(
                    hook,
                    PublicationPhase::SyncTemporary(index),
                    &self.plan,
                    &self._target_lock,
                    || file.sync_all(),
                )?;
            }
            drop(files);
            locked_step(
                hook,
                PublicationPhase::SyncStagedDirectory,
                &self.plan,
                &self._target_lock,
                || self.plan.directory.sync_all(),
            )?;

            for (index, name) in self.plan.data_names.iter().enumerate() {
                locked_step(
                    hook,
                    PublicationPhase::InstallData(index),
                    &self.plan,
                    &self._target_lock,
                    || self.plan.directory.rename_file(&self.plan.temp_names[index], name),
                )?;
            }
            locked_step(
                hook,
                PublicationPhase::SyncInstalledDataDirectory,
                &self.plan,
                &self._target_lock,
                || self.plan.directory.sync_all(),
            )?;

            let commit_index = self.plan.data_names.len();
            locked_step(
                hook,
                PublicationPhase::InstallCommitMarker,
                &self.plan,
                &self._target_lock,
                || {
                    self.plan
                        .directory
                        .rename_file(&self.plan.temp_names[commit_index], &self.plan.commit_name)
                },
            )?;
            locked_step(
                hook,
                PublicationPhase::SyncCommittedDirectory,
                &self.plan,
                &self._target_lock,
                || self.plan.directory.sync_all(),
            )?;
            locked_step(
                hook,
                PublicationPhase::VerifyTargetLock,
                &self.plan,
                &self._target_lock,
                || Ok(()),
            )?;
            Ok(())
        })();

        match result {
            Ok(()) => Ok(()),
            Err(error) => {
                let rollback_errors = rollback(&self.plan, &self._target_lock);
                Err(PublicationError { phase: error.phase, source: error.source, rollback_errors })
            }
        }
    }
}

fn step<T>(
    hook: &mut impl PhaseHook,
    phase: PublicationPhase,
    operation: impl FnOnce() -> io::Result<T>,
) -> Result<T, StepError> {
    hook.before(phase).map_err(|source| StepError { phase, source })?;
    operation().map_err(|source| StepError { phase, source })
}

fn locked_step<T>(
    hook: &mut impl PhaseHook,
    phase: PublicationPhase,
    plan: &PublicationPlan,
    target_lock: &TargetLock,
    operation: impl FnOnce() -> io::Result<T>,
) -> Result<T, StepError> {
    step(hook, phase, || {
        target_lock.verify(
            &plan.directory,
            &plan.requested_path,
            &plan.directory_path,
            &plan.lock_name,
        )?;
        operation()
    })
}

fn validate_plan(data_names: &[String], commit_name: &str) -> io::Result<()> {
    if data_names.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "publication requires at least one data artifact",
        ));
    }
    let mut names = std::collections::BTreeSet::new();
    for name in data_names.iter().map(String::as_str).chain(std::iter::once(commit_name)) {
        if name.is_empty()
            || name == "."
            || name == ".."
            || name.contains('/')
            || name.contains('\\')
            || !Path::new(name).is_relative()
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("artifact name must be one non-empty path component: `{name}`"),
            ));
        }
        if !names.insert(name) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("duplicate artifact name `{name}`"),
            ));
        }
    }
    Ok(())
}

fn validate_control_names(
    data_names: &[String],
    commit_name: &str,
    lock_name: &str,
    temp_names: &[String],
) -> io::Result<()> {
    let mut names = data_names
        .iter()
        .map(String::as_str)
        .chain(std::iter::once(commit_name))
        .collect::<BTreeSet<_>>();
    for name in std::iter::once(lock_name).chain(temp_names.iter().map(String::as_str)) {
        if name.is_empty()
            || name == "."
            || name == ".."
            || name.contains('/')
            || name.contains('\\')
            || !Path::new(name).is_relative()
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("publication control name is not one relative component: `{name}`"),
            ));
        }
        if !names.insert(name) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("publication control name collides with another artifact: `{name}`"),
            ));
        }
    }
    Ok(())
}

fn validate_artifacts(plan: &PublicationPlan, artifacts: &[Artifact<'_>]) -> io::Result<()> {
    let expected_len = plan.data_names.len() + 1;
    if artifacts.len() != expected_len {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("publication expected {expected_len} artifacts, got {}", artifacts.len()),
        ));
    }
    for (index, (artifact, expected)) in artifacts
        .iter()
        .zip(plan.data_names.iter().chain(std::iter::once(&plan.commit_name)))
        .enumerate()
    {
        if artifact.name != expected {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "publication artifact {index} is `{}`, expected `{expected}`",
                    artifact.name
                ),
            ));
        }
    }
    Ok(())
}

fn remove_file_if_present(directory: &DirFd, name: &str) -> io::Result<()> {
    match directory.remove_file(name) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

fn remove_stale_temporaries(plan: &PublicationPlan) -> io::Result<()> {
    for name in plan.directory.read_dir_names()? {
        if !is_publication_temporary(&name, &plan.temp_prefixes) {
            continue;
        }
        // `metadata` opens with no-follow/nonblocking semantics and rejects
        // every non-regular entry. Unexpected objects in the reserved control
        // namespace stop publication rather than being followed or deleted.
        plan.directory.metadata(&name)?;
        match plan.directory.remove_file(&name) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

fn is_publication_temporary(name: &OsStr, prefixes: &[String]) -> bool {
    let Some(name) = name.to_str() else {
        return false;
    };
    prefixes.iter().any(|prefix| {
        name.strip_prefix(prefix.as_str()).is_some_and(|tail| {
            tail.strip_suffix(".tmp").is_some_and(|identity| {
                identity.split_once('-').is_some_and(|(pid, sequence)| {
                    !pid.is_empty()
                        && !sequence.is_empty()
                        && pid.bytes().all(|byte| byte.is_ascii_digit())
                        && sequence.bytes().all(|byte| byte.is_ascii_digit())
                })
            })
        })
    })
}

/// Best-effort rollback always removes the marker first, then every possible
/// data/temp file, and finally syncs the directory. Errors are accumulated so a
/// cleanup failure can never mask the primary publication failure.
fn rollback(plan: &PublicationPlan, target_lock: &TargetLock) -> Vec<String> {
    let mut errors = Vec::new();
    if !rollback_lock_is_valid(plan, target_lock, &mut errors) {
        return errors;
    }
    let commit_path = plan.directory_path.join(&plan.commit_name);
    if let Err(error) = remove_file_if_present(&plan.directory, &plan.commit_name) {
        errors.push(format!("remove({}): {error}", commit_path.display()));
    }
    if !rollback_lock_is_valid(plan, target_lock, &mut errors) {
        return errors;
    }
    if let Err(error) = plan.directory.sync_all() {
        errors.push(format!("sync_dir({}): {error}", plan.directory_path.display()));
    }
    for name in &plan.data_names {
        if !rollback_lock_is_valid(plan, target_lock, &mut errors) {
            return errors;
        }
        let path = plan.directory_path.join(name);
        if let Err(error) = remove_file_if_present(&plan.directory, name) {
            errors.push(format!("remove({}): {error}", path.display()));
        }
    }
    for name in &plan.temp_names {
        if !rollback_lock_is_valid(plan, target_lock, &mut errors) {
            return errors;
        }
        let path = plan.directory_path.join(name);
        if let Err(error) = remove_file_if_present(&plan.directory, name) {
            errors.push(format!("remove({}): {error}", path.display()));
        }
    }
    if !rollback_lock_is_valid(plan, target_lock, &mut errors) {
        return errors;
    }
    if let Err(error) = plan.directory.sync_all() {
        errors.push(format!("sync_dir({}): {error}", plan.directory_path.display()));
    }
    errors
}

fn rollback_lock_is_valid(
    plan: &PublicationPlan,
    target_lock: &TargetLock,
    errors: &mut Vec<String>,
) -> bool {
    match target_lock.verify(
        &plan.directory,
        &plan.requested_path,
        &plan.directory_path,
        &plan.lock_name,
    ) {
        Ok(()) => true,
        Err(error) => {
            errors.push(format!(
                "stop rollback because the target lock identity was lost ({}): {error}",
                plan.directory_path.join(&plan.lock_name).display()
            ));
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    static TEST_SEQUENCE: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new(label: &str) -> Self {
            let sequence = TEST_SEQUENCE.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("trust-thir-publication-{label}-{}-{sequence}", std::process::id()));
            let _ = fs::remove_dir_all(&path);
            fs::create_dir_all(&path).expect("create publication test directory");
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct FailOnce {
        target: PublicationPhase,
        fired: bool,
    }

    impl PhaseHook for FailOnce {
        fn before(&mut self, phase: PublicationPhase) -> io::Result<()> {
            if !self.fired && phase == self.target {
                self.fired = true;
                return Err(io::Error::new(io::ErrorKind::Other, "injected publication failure"));
            }
            Ok(())
        }
    }

    fn names() -> (Vec<String>, String) {
        (
            vec!["sample.trust-ir.bin".to_string(), "sample.trust-ir.txt".to_string()],
            "sample.coverage.json".to_string(),
        )
    }

    fn lock_name() -> &'static str {
        ".sample.coverage.json.trustc-publish.lock"
    }

    fn artifacts<'a>(binary: &'a [u8], text: &'a [u8], marker: &'a [u8]) -> [Artifact<'a>; 3] {
        [
            Artifact { name: "sample.trust-ir.bin", bytes: binary },
            Artifact { name: "sample.trust-ir.txt", bytes: text },
            Artifact { name: "sample.coverage.json", bytes: marker },
        ]
    }

    fn write_stale_set(directory: &Path) {
        fs::write(directory.join("sample.trust-ir.bin"), b"old-bin").unwrap();
        fs::write(directory.join("sample.trust-ir.txt"), b"old-text").unwrap();
        fs::write(directory.join("sample.coverage.json"), b"old-marker").unwrap();
        DirFd::open(directory).unwrap().sync_all().unwrap();
    }

    fn assert_no_current_set(directory: &Path) {
        for name in ["sample.trust-ir.bin", "sample.trust-ir.txt", "sample.coverage.json"] {
            assert!(!directory.join(name).exists(), "partial/current artifact survived: {name}");
        }
        if directory.is_dir() {
            for entry in fs::read_dir(directory).unwrap() {
                let name = entry.unwrap().file_name();
                assert!(
                    !name.to_string_lossy().contains(".trustc-publish-"),
                    "temporary publication artifact survived: {}",
                    name.to_string_lossy()
                );
            }
        }
    }

    #[test]
    fn successful_publication_replaces_stale_set_and_installs_marker_last() {
        let directory = TestDirectory::new("success");
        write_stale_set(directory.path());
        let (data_names, commit_name) = names();
        let prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect("invalidate stale artifact set");

        assert_no_current_set(directory.path());
        prepared
            .publish(&artifacts(b"new-bin", b"new-text", b"new-marker"))
            .expect("publish replacement artifact set");

        assert_eq!(fs::read(directory.path().join("sample.trust-ir.bin")).unwrap(), b"new-bin");
        assert_eq!(fs::read(directory.path().join("sample.trust-ir.txt")).unwrap(), b"new-text");
        assert_eq!(fs::read(directory.path().join("sample.coverage.json")).unwrap(), b"new-marker");
        assert!(directory.path().join(lock_name()).is_file());
    }

    #[test]
    fn every_preparation_and_publication_phase_rolls_back_without_stale_or_mixed_set() {
        let phases = [
            PublicationPhase::VerifyTargetLock,
            PublicationPhase::InvalidateCommitMarker,
            PublicationPhase::SyncInvalidatedMarkerDirectory,
            PublicationPhase::InvalidateData(0),
            PublicationPhase::InvalidateData(1),
            PublicationPhase::InvalidateStaleTemporaries,
            PublicationPhase::SyncInvalidatedSetDirectory,
            PublicationPhase::CreateTemporary(0),
            PublicationPhase::CreateTemporary(1),
            PublicationPhase::CreateTemporary(2),
            PublicationPhase::WriteTemporary(0),
            PublicationPhase::WriteTemporary(1),
            PublicationPhase::WriteTemporary(2),
            PublicationPhase::SyncTemporary(0),
            PublicationPhase::SyncTemporary(1),
            PublicationPhase::SyncTemporary(2),
            PublicationPhase::SyncStagedDirectory,
            PublicationPhase::InstallData(0),
            PublicationPhase::InstallData(1),
            PublicationPhase::SyncInstalledDataDirectory,
            PublicationPhase::InstallCommitMarker,
            PublicationPhase::SyncCommittedDirectory,
        ];

        for phase in phases {
            let directory = TestDirectory::new("phase-failure");
            write_stale_set(directory.path());
            let (data_names, commit_name) = names();
            let mut hook = FailOnce { target: phase, fired: false };
            let result = PreparedPublication::prepare_with_hook(
                directory.path().to_path_buf(),
                data_names,
                commit_name,
                &mut hook,
            )
            .and_then(|prepared| {
                prepared.publish_with_hook(
                    &artifacts(b"new-bin", b"new-text", b"new-marker"),
                    &mut hook,
                )
            });

            assert!(hook.fired, "failure phase was not reached: {phase:?}");
            let error = result.expect_err("injected phase must fail publication");
            assert_eq!(error.phase, phase);
            assert_no_current_set(directory.path());
        }
    }

    #[test]
    fn pre_lock_failures_do_not_mutate_a_possibly_active_generation() {
        for phase in [
            PublicationPhase::CreateDirectory,
            PublicationPhase::CanonicalizeDirectory,
            PublicationPhase::OpenDirectory,
            PublicationPhase::AcquireTargetLock,
        ] {
            let directory = TestDirectory::new("pre-lock-failure");
            write_stale_set(directory.path());
            let (data_names, commit_name) = names();
            let mut hook = FailOnce { target: phase, fired: false };

            let error = PreparedPublication::prepare_with_hook(
                directory.path().to_path_buf(),
                data_names,
                commit_name,
                &mut hook,
            )
            .expect_err("injected pre-lock failure must stop preparation");

            assert!(hook.fired, "failure phase was not reached: {phase:?}");
            assert_eq!(error.phase, phase);
            assert_eq!(fs::read(directory.path().join("sample.trust-ir.bin")).unwrap(), b"old-bin");
            assert_eq!(
                fs::read(directory.path().join("sample.trust-ir.txt")).unwrap(),
                b"old-text"
            );
            assert_eq!(
                fs::read(directory.path().join("sample.coverage.json")).unwrap(),
                b"old-marker"
            );
        }
    }

    #[test]
    fn every_partial_stale_file_combination_is_invalidated_before_semantic_work() {
        for mask in 0_u8..8 {
            let directory = TestDirectory::new("partial-stale");
            for (bit, name) in
                ["sample.trust-ir.bin", "sample.trust-ir.txt", "sample.coverage.json"]
                    .into_iter()
                    .enumerate()
            {
                if mask & (1 << bit) != 0 {
                    fs::write(directory.path().join(name), format!("stale-{mask}-{bit}")).unwrap();
                }
            }
            let (data_names, commit_name) = names();
            let _prepared = PreparedPublication::prepare(
                directory.path().to_path_buf(),
                data_names,
                commit_name,
            )
            .expect("invalidate every partial stale set");
            assert_no_current_set(directory.path());
        }
    }

    #[test]
    fn crashed_prior_process_temporaries_are_removed_through_the_directory_anchor() {
        let directory = TestDirectory::new("stale-temporaries");
        let stale = [
            ".sample.trust-ir.bin.trustc-publish-999991-41.tmp",
            ".sample.trust-ir.txt.trustc-publish-999992-42.tmp",
            ".sample.coverage.json.trustc-publish-999993-43.tmp",
        ];
        for name in stale {
            fs::write(directory.path().join(name), b"abandoned").unwrap();
        }
        let unrelated = ".other.trustc-publish-999994-44.tmp";
        fs::write(directory.path().join(unrelated), b"unrelated").unwrap();
        let (data_names, commit_name) = names();

        let _prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect("remove abandoned transaction temporaries");

        for name in stale {
            assert!(!directory.path().join(name).exists(), "stale temporary survived: {name}");
        }
        assert_eq!(fs::read(directory.path().join(unrelated)).unwrap(), b"unrelated");
    }

    #[test]
    fn unremovable_stale_data_still_loses_commit_marker_first() {
        let directory = TestDirectory::new("unremovable-stale");
        write_stale_set(directory.path());
        fs::remove_file(directory.path().join("sample.trust-ir.bin")).unwrap();
        fs::create_dir(directory.path().join("sample.trust-ir.bin")).unwrap();
        let (data_names, commit_name) = names();

        let error =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect_err("a directory at a data path must fail closed");

        assert_eq!(error.phase, PublicationPhase::InvalidateData(0));
        assert!(!directory.path().join("sample.coverage.json").exists());
        assert!(!directory.path().join("sample.trust-ir.txt").exists());
        assert!(directory.path().join("sample.trust-ir.bin").is_dir());
    }

    #[test]
    fn malformed_or_mismatched_plans_fail_before_writing() {
        let directory = TestDirectory::new("invalid-plan");
        let error = PreparedPublication::prepare(
            directory.path().to_path_buf(),
            vec!["../escape".to_string()],
            "marker".to_string(),
        )
        .expect_err("parent traversal must be rejected");
        assert_eq!(error.phase, PublicationPhase::ValidatePlan);

        let (data_names, commit_name) = names();
        let prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .unwrap();
        let error = prepared
            .publish(&[
                Artifact { name: "sample.trust-ir.txt", bytes: b"wrong-order" },
                Artifact { name: "sample.trust-ir.bin", bytes: b"wrong-order" },
                Artifact { name: "sample.coverage.json", bytes: b"marker" },
            ])
            .expect_err("artifact order/name mismatch must fail closed");
        assert_eq!(error.phase, PublicationPhase::ValidatePlan);
        assert_no_current_set(directory.path());
    }

    #[test]
    fn a_second_in_process_writer_cannot_observe_or_mutate_a_partial_install() {
        use std::sync::mpsc;
        use std::time::Duration;

        struct PauseBeforeSecondInstall {
            reached: mpsc::SyncSender<()>,
            resume: mpsc::Receiver<()>,
        }

        impl PhaseHook for PauseBeforeSecondInstall {
            fn before(&mut self, phase: PublicationPhase) -> io::Result<()> {
                if phase == PublicationPhase::InstallData(1) {
                    self.reached.send(()).unwrap();
                    self.resume.recv().unwrap();
                }
                Ok(())
            }
        }

        let directory = TestDirectory::new("same-process-writers");
        let (data_names, commit_name) = names();
        let prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .unwrap();
        let (reached_tx, reached_rx) = mpsc::sync_channel(0);
        let (resume_tx, resume_rx) = mpsc::sync_channel(0);
        let publisher = std::thread::spawn(move || {
            let mut hook = PauseBeforeSecondInstall { reached: reached_tx, resume: resume_rx };
            prepared.publish_with_hook(
                &artifacts(b"first-bin", b"first-text", b"first-marker"),
                &mut hook,
            )
        });

        reached_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("publisher reached its partial-install boundary");
        assert_eq!(fs::read(directory.path().join("sample.trust-ir.bin")).unwrap(), b"first-bin");
        assert!(!directory.path().join("sample.trust-ir.txt").exists());
        assert!(!directory.path().join("sample.coverage.json").exists());

        let (data_names, commit_name) = names();
        let error =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect_err("a second in-process writer must fail without touching the target");
        assert_eq!(error.phase, PublicationPhase::AcquireTargetLock);
        assert_eq!(error.source.kind(), io::ErrorKind::WouldBlock);
        assert_eq!(fs::read(directory.path().join("sample.trust-ir.bin")).unwrap(), b"first-bin");

        resume_tx.send(()).unwrap();
        publisher.join().unwrap().unwrap();
        assert_eq!(fs::read(directory.path().join("sample.trust-ir.txt")).unwrap(), b"first-text");
        assert_eq!(
            fs::read(directory.path().join("sample.coverage.json")).unwrap(),
            b"first-marker"
        );
    }

    #[test]
    fn distinct_in_process_target_spellings_share_the_pre_open_directory_guard() {
        let directory = TestDirectory::new("same-process-alias-guard");
        let (data_names, commit_name) = names();
        let _first =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect("first target owns the directory's pre-open guard");

        let error = PreparedPublication::prepare(
            directory.path().to_path_buf(),
            vec!["SAMPLE.trust-ir.bin".into(), "SAMPLE.trust-ir.txt".into()],
            "SAMPLE.coverage.json".into(),
        )
        .expect_err("a differently spelled in-process target must not open an aliasing sentinel");

        assert_eq!(error.phase, PublicationPhase::AcquireTargetLock);
        assert_eq!(error.source.kind(), io::ErrorKind::WouldBlock);
        let lock_entries = fs::read_dir(directory.path())
            .unwrap()
            .filter_map(Result::ok)
            .filter(|entry| entry.file_name().to_string_lossy().ends_with(".trustc-publish.lock"))
            .count();
        assert_eq!(
            lock_entries, 1,
            "the alias guard must fail before creating a second sentinel entry"
        );
    }

    #[cfg(unix)]
    #[test]
    fn directory_path_swap_is_detected_without_publishing_to_either_identity() {
        let directory = TestDirectory::new("path-swap");
        let moved = directory.path().with_extension("anchored");
        let _ = fs::remove_dir_all(&moved);
        let (data_names, commit_name) = names();
        let prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .unwrap();

        fs::rename(directory.path(), &moved).unwrap();
        fs::create_dir(directory.path()).unwrap();
        let error = prepared
            .publish(&artifacts(b"anchored-bin", b"anchored-text", b"anchored-marker"))
            .expect_err("requested path identity changed");

        assert_eq!(error.phase, PublicationPhase::CreateTemporary(0));
        assert!(!error.rollback_errors.is_empty());
        assert!(fs::read_dir(directory.path()).unwrap().next().is_none());
        assert!(!moved.join("sample.trust-ir.bin").exists());
        assert!(!moved.join("sample.trust-ir.txt").exists());
        assert!(!moved.join("sample.coverage.json").exists());

        fs::remove_dir(directory.path()).unwrap();
        fs::rename(&moved, directory.path()).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn symlink_and_hardlinked_lock_sentinels_fail_closed_without_following() {
        use std::os::unix::fs::symlink;

        for hardlink in [false, true] {
            let directory = TestDirectory::new("unsafe-lock-sentinel");
            write_stale_set(directory.path());
            let outside =
                directory.path().with_extension(if hardlink { "hardlink" } else { "symlink" });
            let _ = fs::remove_file(&outside);
            fs::write(&outside, b"outside").unwrap();
            let sentinel = directory.path().join(lock_name());
            if hardlink {
                fs::hard_link(&outside, &sentinel).unwrap();
            } else {
                symlink(&outside, &sentinel).unwrap();
            }
            let (data_names, commit_name) = names();

            let error = PreparedPublication::prepare(
                directory.path().to_path_buf(),
                data_names,
                commit_name,
            )
            .expect_err("an unsafe lock entry must never be followed or locked");

            assert_eq!(error.phase, PublicationPhase::AcquireTargetLock);
            assert_eq!(fs::read(&outside).unwrap(), b"outside");
            assert_eq!(
                fs::read(directory.path().join("sample.coverage.json")).unwrap(),
                b"old-marker",
                "pre-lock failure must not race a possibly active publisher"
            );
            fs::remove_file(&outside).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn non_regular_stale_temporary_is_refused_without_following() {
        use std::os::unix::fs::symlink;

        let directory = TestDirectory::new("unsafe-stale-temporary");
        write_stale_set(directory.path());
        let outside = directory.path().with_extension("outside-temp");
        let _ = fs::remove_file(&outside);
        fs::write(&outside, b"outside").unwrap();
        let stale = directory.path().join(".sample.trust-ir.bin.trustc-publish-1234-7.tmp");
        symlink(&outside, &stale).unwrap();
        let (data_names, commit_name) = names();

        let error =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect_err("a non-regular reserved temporary must fail closed");

        assert_eq!(error.phase, PublicationPhase::InvalidateStaleTemporaries);
        assert_eq!(fs::read(&outside).unwrap(), b"outside");
        assert!(!directory.path().join("sample.coverage.json").exists());
        fs::remove_file(&outside).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn replacing_the_locked_sentinel_is_detected_and_rolls_back() {
        let directory = TestDirectory::new("replaced-lock-sentinel");
        let (data_names, commit_name) = names();
        let prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .unwrap();
        let sentinel = directory.path().join(lock_name());
        let displaced = directory.path().join("displaced-lock-sentinel");
        fs::rename(&sentinel, &displaced).unwrap();
        fs::write(&sentinel, b"replacement").unwrap();
        fs::write(directory.path().join("sample.trust-ir.bin"), b"concurrent-bin").unwrap();
        fs::write(directory.path().join("sample.trust-ir.txt"), b"concurrent-text").unwrap();
        fs::write(directory.path().join("sample.coverage.json"), b"concurrent-marker").unwrap();

        let error = prepared
            .publish(&artifacts(b"new-bin", b"new-text", b"new-marker"))
            .expect_err("a replaced lock entry must invalidate publication");

        assert_eq!(error.phase, PublicationPhase::CreateTemporary(0));
        assert!(!error.rollback_errors.is_empty());
        assert_eq!(
            fs::read(directory.path().join("sample.trust-ir.bin")).unwrap(),
            b"concurrent-bin"
        );
        assert_eq!(
            fs::read(directory.path().join("sample.trust-ir.txt")).unwrap(),
            b"concurrent-text"
        );
        assert_eq!(
            fs::read(directory.path().join("sample.coverage.json")).unwrap(),
            b"concurrent-marker"
        );
    }

    #[cfg(unix)]
    #[test]
    fn cross_process_lock_is_released_after_process_death() {
        use std::process::{Child, Command, Stdio};
        use std::thread;
        use std::time::{Duration, Instant};

        const CHILD_MODE: &str = "TRUST_ARTIFACT_PUBLICATION_LOCK_CHILD";
        const CHILD_DIRECTORY: &str = "TRUST_ARTIFACT_PUBLICATION_LOCK_DIRECTORY";
        const CHILD_READY: &str = "TRUST_ARTIFACT_PUBLICATION_LOCK_READY";

        if std::env::var_os(CHILD_MODE).is_some() {
            let directory = PathBuf::from(std::env::var_os(CHILD_DIRECTORY).unwrap());
            let ready = PathBuf::from(std::env::var_os(CHILD_READY).unwrap());
            let (data_names, commit_name) = names();
            let _prepared = PreparedPublication::prepare(directory, data_names, commit_name)
                .expect("child acquires cross-process publication lock");
            fs::write(ready, b"ready").unwrap();
            loop {
                thread::sleep(Duration::from_secs(30));
            }
        }

        struct ChildGuard(Child);

        impl ChildGuard {
            fn terminate(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }

        impl Drop for ChildGuard {
            fn drop(&mut self) {
                self.terminate();
            }
        }

        fn spawn_child(directory: &Path, ready: &Path) -> ChildGuard {
            ChildGuard(
                Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "artifact_publication::tests::cross_process_lock_is_released_after_process_death",
                    "--nocapture",
                ])
                .env("TRUST_ARTIFACT_PUBLICATION_LOCK_CHILD", "1")
                .env("TRUST_ARTIFACT_PUBLICATION_LOCK_DIRECTORY", directory)
                .env("TRUST_ARTIFACT_PUBLICATION_LOCK_READY", ready)
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .unwrap(),
            )
        }

        fn wait_ready(child: &mut ChildGuard, ready: &Path) {
            let deadline = Instant::now() + Duration::from_secs(5);
            while !ready.exists() {
                assert!(
                    child.0.try_wait().unwrap().is_none(),
                    "lock child exited before acquiring the target"
                );
                assert!(Instant::now() < deadline, "timed out waiting for lock child");
                thread::sleep(Duration::from_millis(10));
            }
        }

        let directory = TestDirectory::new("cross-process-crash");
        write_stale_set(directory.path());
        let ready_a = directory.path().join("child-a.ready");
        let ready_b = directory.path().join("child-b.ready");
        let mut child_a = spawn_child(directory.path(), &ready_a);
        wait_ready(&mut child_a, &ready_a);
        assert!(!directory.path().join("sample.coverage.json").exists());

        let mut child_b = spawn_child(directory.path(), &ready_b);
        thread::sleep(Duration::from_millis(300));
        assert!(!ready_b.exists(), "second process acquired a live writer target");

        child_a.terminate();
        wait_ready(&mut child_b, &ready_b);
        child_b.terminate();

        let (data_names, commit_name) = names();
        let prepared =
            PreparedPublication::prepare(directory.path().to_path_buf(), data_names, commit_name)
                .expect("parent reacquires lock after both child crashes");
        prepared.publish(&artifacts(b"parent-bin", b"parent-text", b"parent-marker")).unwrap();
        assert_eq!(
            fs::read(directory.path().join("sample.coverage.json")).unwrap(),
            b"parent-marker"
        );
    }
}
