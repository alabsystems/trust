//! Register observed existing work as durable logical coordination debt.
//!
//! An observed PID is never CPU, process-control or release authority. This
//! operation starts/signals no target, exports no descriptors and creates no
//! native CPU pool. Only the actual complete original coordination claim may
//! publish its corresponding record before closing its transient flocks.

use std::num::NonZeroU64;

use trust_build_cpu::Pool;
use trust_sha2::{Digest, Sha256};

use super::*;

#[path = "adoption/identity.rs"]
mod identity;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Publication {
    /// This owner has not attempted a new publication. This does not say
    /// that no prior or unrelated logical debt exists in the registry.
    NotPublished,
    /// A publication syscall or later bookend failed; never replay it
    /// automatically or interpret this error as absence of logical debt.
    Unknown,
}

#[derive(Debug)]
pub struct AdoptionError {
    source: io::Error,
    publication: Publication,
}
impl AdoptionError {
    pub fn publication(&self) -> Publication {
        self.publication
    }
    fn before(source: io::Error) -> Self {
        Self { source, publication: Publication::NotPublished }
    }
}
impl std::fmt::Display for AdoptionError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "adoption {:?}: {}", self.publication, self.source)
    }
}
impl std::error::Error for AdoptionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/// Publication observation, not an original lease, grant or recovery handle.
#[derive(Debug, Serialize)]
pub struct AdoptionObservation {
    pub pid: u32,
    pub birth: String,
    pub exclusive: bool,
    pub lease_paths: Vec<PathBuf>,
}
#[derive(Debug, Serialize)]
#[serde(tag = "state", content = "observation", rename_all = "snake_case")]
pub enum AdoptionOutcome {
    Registered(AdoptionObservation),
    AlreadyRegistered(AdoptionObservation),
}

pub struct Adoption {
    coordinator: Coordinator,
    cwd: Directory,
    identity: identity::Identity,
    pool: Pool,
    // A post-publication error permanently disables this actual attempt.
    publication_started: bool,
    poisoned: bool,
}

impl Adoption {
    pub fn for_current_user(
        pid: u32,
        worktree_lock: Option<PathBuf>,
        exclusive: bool,
        minimum_memory_bytes: NonZeroU64,
    ) -> Result<Self, AdoptionError> {
        (|| {
            reject_inherited()?;
            let cwd = Directory::open(&fs::canonicalize(std::env::current_dir()?)?)?;
            let identity = identity::checked(pid, &cwd)?;
            let namespace = fs::canonicalize(account_home()?.join(".cache/build-slot"))?;
            let locations = Locations::current()?;
            if locations.namespace != namespace {
                return Err(invalid(
                    "native PID adoption requires the canonical machine namespace",
                ));
            }
            let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?
                .ok_or_else(|| invalid("original native CPU manifest is unavailable"))?;
            // Activated mixed domains have no qualified PID-debt publication
            // bridge. Observe/refuse BEFORE creating queue/registry metadata.
            let transaction = pool
                .try_legacy_fixed_transaction()?
                .ok_or_else(|| io::Error::from(io::ErrorKind::WouldBlock))?;
            drop(transaction);
            let worktree_lock = worktree_lock
                .map(|path| {
                    validate_path(&path)?;
                    super::super::adopted::canonical_location(&path)
                })
                .transpose()?;
            let required = Requirements::new(
                worktree_lock,
                (pool.slots().get() / 6).max(1),
                1,
                exclusive,
                minimum_memory_bytes.get(),
            )?;
            let coordinator = Coordinator::open_selected(&namespace, &locations.adopted, required)?;
            Ok(Self {
                coordinator,
                cwd,
                identity,
                pool,
                publication_started: false,
                poisoned: false,
            })
        })()
        .map_err(AdoptionError::before)
    }

    /// Nonblocking registration attempt. Waiting retains the original ticket.
    /// No target is started, resumed, signalled or assigned a CPU/GNU budget.
    pub fn attempt(&mut self) -> Result<Attempt<AdoptionOutcome>, AdoptionError> {
        if self.coordinator.ticket.owner != std::process::id() {
            return Err(AdoptionError::before(invalid(
                "forked adoption copy is not the original publisher",
            )));
        }
        if self.poisoned {
            return Err(AdoptionError {
                source: invalid("adoption publication owner is poisoned"),
                publication: if self.publication_started {
                    Publication::Unknown
                } else {
                    Publication::NotPublished
                },
            });
        }
        // Unwind is unresolved too. Only a normal known result may reopen
        // this same attempt; no callback/panic can silently resume dispatch.
        self.poisoned = true;
        let result = self.attempt_observed(trust_build_cpu::available_memory());
        if result.is_ok() {
            self.poisoned = false;
        }
        result.map_err(|source| {
            self.poisoned = true;
            AdoptionError {
                source,
                publication: if self.publication_started {
                    Publication::Unknown
                } else {
                    Publication::NotPublished
                },
            }
        })
    }

    fn attempt_observed(&mut self, memory: Option<u64>) -> io::Result<Attempt<AdoptionOutcome>> {
        let fresh = identity::checked(self.identity.pid, &self.cwd)?;
        if fresh != self.identity {
            return Err(invalid("original adoption process changed while waiting"));
        }
        let registry = Registry::open(&self.coordinator.directory)?;
        // Existing virtual debt would prevent a second physical acquisition.
        // This is only a checked publication observation, never a new guard.
        if let Some(guard) = registry.try_guard()? {
            if let Some(prior) = guard.prior(&self.identity, &self.coordinator.ticket.required)? {
                identity::checked(self.identity.pid, &self.cwd).and_then(|fresh| {
                    if fresh == self.identity {
                        Ok(())
                    } else {
                        Err(invalid("adopted process changed during repeat observation"))
                    }
                })?;
                guard.check()?;
                return Ok(Attempt::Admitted(AdoptionOutcome::AlreadyRegistered(prior)));
            }
        } else {
            return Ok(Attempt::Waiting(super::super::Waiting::RegistryBusy));
        }
        #[cfg(test)]
        test_hook(PublishStage::AfterEarlyPrior, &registry.directory.path)?;

        let original = &self.identity;
        let cwd = &self.cwd;
        let pool = &self.pool;
        let publication_started = &mut self.publication_started;
        let required = self.coordinator.ticket.required.clone();
        self.coordinator.attempt_with(memory, 1, |mut reservation| {
            if reservation.exclusive && !reservation.try_drain_exclusive()? {
                return Ok(None);
            }
            let Some(_native_transaction) = pool.try_legacy_fixed_transaction()? else {
                return Ok(None);
            };
            let Some(guard) = registry.try_guard()? else { return Ok(None) };
            if let Some(prior) = guard.prior(original, &required)? {
                if identity::checked(original.pid, cwd)? != *original {
                    return Err(invalid("adopted process changed during late repeat observation"));
                }
                reservation.check_current()?;
                guard.check()?;
                return Ok(Some(AdoptionOutcome::AlreadyRegistered(prior)));
            }
            if identity::checked(original.pid, cwd)? != *original {
                return Err(invalid("process changed before adoption publication"));
            }
            reservation.check_current()?;
            let observation =
                guard.publish(&reservation, &required, original, cwd, publication_started)?;
            reservation.check_current()?;
            cwd.check()?;
            // Publication cannot undo an already visible debt if a final
            // process observation fails. The caller receives Unknown instead.
            if identity::checked(original.pid, cwd)? != *original {
                return Err(invalid("process changed after adoption publication"));
            }
            guard.check()?;
            Ok(Some(AdoptionOutcome::Registered(observation)))
        })
    }
}

fn reject_inherited() -> io::Result<()> {
    for name in [
        "BUILD_SLOT_HELD",
        "ATERM_RESOURCE_JOB_V3",
        "ATERM_SDK_LEASE_V3",
        "TRUST_CPU_HANDOFF",
        "TRUST_CPU_IMPLICIT_FD",
        "ATERM_WORKLOAD_CPU_FDS_V1",
        "TRUST_FIXED_CLAIM_HANDOFF_V1",
        FIXED_HANDOFF_ENV,
    ] {
        if std::env::var_os(name).is_some() {
            return Err(invalid("PID adoption must run outside an inherited resource admission"));
        }
    }
    Ok(())
}

struct Registry {
    namespace: Directory,
    directory: Directory,
}
struct RegistryGuard<'a> {
    registry: &'a Registry,
    file: File,
}

#[derive(Serialize)]
struct PublicationRecord<'a> {
    schema: u32,
    adopted: bool,
    pid: u32,
    identity: &'a identity::Identity,
    pool: &'a Path,
    worktree: Option<&'a Path>,
    leases: &'a [PathBuf],
    exclusive: bool,
    cmd: &'a Path,
    cwd: &'a Path,
    started: f64,
}
impl Registry {
    fn open(namespace: &Directory) -> io::Result<Self> {
        namespace.check()?;
        let name = std::ffi::CString::new("adopted").unwrap();
        if unsafe { libc::mkdirat(namespace.file.as_raw_fd(), name.as_ptr(), 0o700) } != 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::AlreadyExists {
                return Err(error);
            }
        }
        let directory = Directory::open(&namespace.path.join("adopted"))?;
        namespace.check()?;
        let namespace =
            Directory { path: namespace.path.clone(), file: namespace.file.try_clone()? };
        Ok(Self { namespace, directory })
    }
    fn try_guard(&self) -> io::Result<Option<RegistryGuard<'_>>> {
        let file = self.directory.open_file("registration.lock", true)?;
        if !try_exclusive(&file)? {
            return Ok(None);
        }
        self.directory.check_file("registration.lock", &file)?;
        Ok(Some(RegistryGuard { registry: self, file }))
    }
}
impl RegistryGuard<'_> {
    fn check(&self) -> io::Result<()> {
        self.registry.namespace.check()?;
        self.registry.directory.check_file("registration.lock", &self.file)
    }
    fn prior(
        &self,
        identity: &identity::Identity,
        required: &Requirements,
    ) -> io::Result<Option<AdoptionObservation>> {
        self.check()?;
        let directory = &self.registry.directory;
        let mut found = None;
        for name in directory.entries()? {
            if !name.as_bytes().ends_with(b".json") {
                continue;
            }
            let file = directory.open_file(&name, false)?;
            let bytes = read_record(&file)?;
            let record = super::super::adopted::read_valid_record(&bytes)?;
            directory.check_file(&name, &file)?;
            if record.pid == identity.pid && record.birth == identity.birth {
                if found.is_some()
                    || record.pool != self.registry.directory.path.parent().unwrap()
                    || record.worktree.as_deref() != required.worktree()
                    || (required.exclusive && !record.exclusive)
                {
                    return Err(invalid(
                        "existing adoption conflicts with the complete requested claim",
                    ));
                }
                self.check_prior_paths(&record, required)?;
                found = Some(AdoptionObservation {
                    pid: identity.pid,
                    birth: identity.birth.clone(),
                    exclusive: record.exclusive,
                    lease_paths: record.leases,
                });
            }
            if read_record(&file)? != bytes {
                return Err(invalid("existing adoption record changed during repeat observation"));
            }
        }
        self.check()?;
        Ok(found)
    }

    fn check_prior_paths(
        &self,
        record: &super::super::adopted::ValidRecord,
        required: &Requirements,
    ) -> io::Result<()> {
        let mut paths = record.leases.iter().cloned().collect::<std::collections::BTreeSet<_>>();
        if paths.len() != record.leases.len() {
            return Err(invalid("existing adoption repeats a claim member"));
        }
        if let Some(worktree) = &record.worktree {
            if !paths.remove(worktree) {
                return Err(invalid("existing adoption lacks its exact worktree member"));
            }
        }
        if paths.is_empty() {
            return Err(invalid("existing adoption has no actual slot members"));
        }
        let namespace = &self.registry.namespace;
        for path in &paths {
            if path.parent() != Some(namespace.path.as_path()) {
                return Err(invalid("existing adoption slot is outside its original namespace"));
            }
            let index = path
                .file_name()
                .and_then(|name| name.to_str())
                .and_then(|name| name.strip_prefix("slot-"))
                .filter(|tail| !tail.is_empty() && tail.bytes().all(|byte| byte.is_ascii_digit()))
                .and_then(|tail| tail.parse::<u32>().ok())
                .ok_or_else(|| {
                    invalid("existing adoption member is not a bounded original slot")
                })?;
            if index >= trust_build_cpu::MAX_SLOTS || (!record.exclusive && index >= required.slots)
            {
                return Err(invalid("existing adoption slot is outside the requested pool"));
            }
        }
        if record.exclusive {
            let expected = slot_names(namespace, required.slots)?
                .into_iter()
                .map(|name| namespace.path.join(name))
                .collect::<std::collections::BTreeSet<_>>();
            if paths != expected {
                return Err(invalid(
                    "prior exclusive registration does not cover the complete current original population",
                ));
            }
        } else if paths.len() != 1 {
            return Err(invalid("prior shared adoption has an unsupported claim width"));
        }
        self.check()
    }
    fn publish(
        &self,
        reservation: &Reservation,
        required: &Requirements,
        identity: &identity::Identity,
        cwd: &Directory,
        publication_started: &mut bool,
    ) -> io::Result<AdoptionObservation> {
        self.check()?;
        reservation.check_current()?;
        let count = reservation
            .held
            .len()
            .checked_sub(1)
            .ok_or_else(|| invalid("original adoption claim has no admission fence"))?;
        let admission = &reservation.held[count];
        if admission.name != "admission.lock" || admission.directory.path != reservation.namespace {
            return Err(invalid("original admission fence binding changed"));
        }
        // admission.lock is temporary coordination, not virtual debt. Shared
        // adoption must leave other actual free shares usable after publication.
        let mut paths = Vec::new();
        let mut path_bytes = 0_usize;
        for lease in reservation.held[..count].iter().chain(&reservation.slots) {
            let path = fs::canonicalize(lease.path())?;
            path_bytes = path_bytes
                .checked_add(serde_json::to_vec(&path).map_err(io::Error::other)?.len())
                .ok_or_else(|| invalid("adoption path population overflows"))?;
            if path_bytes as u64 > MAX_RECORD {
                return Err(invalid("complete adoption path population exceeds the record bound"));
            }
            paths.push(path);
        }
        let worktree = required.worktree().map(fs::canonicalize).transpose()?;
        let value = PublicationRecord {
            schema: 1,
            adopted: true,
            pid: identity.pid,
            identity,
            pool: &reservation.namespace,
            worktree: worktree.as_deref(),
            leases: &paths,
            exclusive: reservation.exclusive,
            cmd: &identity.executable,
            cwd: &cwd.path,
            started: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_err(io::Error::other)?
                .as_secs_f64(),
        };
        let bytes = serde_json::to_vec(&value).map_err(io::Error::other)?;
        if bytes.len() as u64 > MAX_RECORD {
            return Err(invalid("complete adoption record exceeds its bound"));
        }
        super::super::adopted::read_valid_record(&bytes)?;
        let key = format!(
            "{:x}",
            Sha256::digest(format!("{}:{}", identity.pid, identity.birth).as_bytes())
        );
        let name = format!("{key}.json");
        let temporary = format!(".pending-{key}-{}", std::process::id());
        let directory = &self.registry.directory;
        let mut file = directory.create_file(&temporary, true, true)?;
        let mut attempted = false;
        let result = (|| {
            file.write_all(&bytes)?;
            file.sync_all()?;
            directory.check_file(&temporary, &file)?;
            if read_record(&file)? != bytes {
                return Err(invalid("original complete adoption bytes changed before publication"));
            }
            self.check()?;
            reservation.check_current()?;
            #[cfg(test)]
            test_hook(PublishStage::BeforeLink, &directory.path)?;
            let from = std::ffi::CString::new(temporary.as_str()).unwrap();
            let to = std::ffi::CString::new(name.as_str()).unwrap();
            *publication_started = true;
            attempted = true;
            // Atomic no-overwrite publication. The temporary second hardlink
            // is removed under the same registration lock before readers may
            // validate nlink==1. A crash leaves an explicit unknown barrier.
            if unsafe {
                libc::linkat(
                    directory.file.as_raw_fd(),
                    from.as_ptr(),
                    directory.file.as_raw_fd(),
                    to.as_ptr(),
                    0,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            #[cfg(test)]
            test_hook(PublishStage::AfterLink, &directory.path)?;
            if unsafe { libc::unlinkat(directory.file.as_raw_fd(), from.as_ptr(), 0) } != 0 {
                return Err(io::Error::last_os_error());
            }
            directory.file.sync_all()?;
            directory.check_file(&name, &file)?;
            if read_record(&file)? != bytes {
                return Err(invalid("original adopted record changed after publication"));
            }
            self.check()?;
            #[cfg(test)]
            test_hook(PublishStage::AfterPublish, &directory.path)?;
            Ok(AdoptionObservation {
                pid: identity.pid,
                birth: identity.birth.clone(),
                exclusive: reservation.exclusive,
                lease_paths: paths,
            })
        })();
        if !attempted {
            let _ = directory.remove(&temporary, &file);
        }
        result
    }
}

#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum PublishStage {
    AfterEarlyPrior,
    BeforeLink,
    AfterLink,
    AfterPublish,
}
#[cfg(test)]
type PublishHook = Box<dyn FnMut(PublishStage, &Path) -> io::Result<()>>;
#[cfg(test)]
thread_local! {
    static PUBLISH_HOOK: std::cell::RefCell<Option<PublishHook>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
fn test_hook(stage: PublishStage, directory: &Path) -> io::Result<()> {
    PUBLISH_HOOK.with(|hook| match &mut *hook.borrow_mut() {
        Some(hook) => hook(stage, directory),
        None => Ok(()),
    })
}

#[cfg(test)]
#[path = "adoption/tests.rs"]
mod tests;
