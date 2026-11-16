// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Native process descriptor admission shared by retained Host/Root callers.
//! This coordinates the actual process table and checked soft limit. It grants
//! no CPU, SDK, Ready, execution or proof authority. Callers retain their real
//! paid preparation, source/SDK and retirement owners separately.
//! Checked limit acquisition leaves a process-owned pool at the raised soft
//! limit, including failed materialization and final target drop. Scoped charges
//! return; the shared OS limit is never unsafely restored underneath other live
//! budgets, files or callers. The original hard limit is never changed.

use ::std::collections::BTreeMap;
use ::std::io;
use ::std::path::{Path, PathBuf};
use ::std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use ::std::sync::{Arc, Mutex, OnceLock};
use ::std::time::Instant;
use trust_resource_provenance::process;
use trust_resource_provenance::program::produced::{
    HeldOutputRoot, HeldRootDirectory, HeldRootFile, PublicationExclusions,
};
use trust_resource_provenance::program::{
    FileObservation, HeldDirectoryInput, HeldPackageSource, HeldProgram, HeldRustTargetSysroot,
    PackageEntry, PackageSourcePlan, RustTargetSysrootPlan,
};

use crate::FileIdentity;

const RESERVE: usize = 128;
const EXTRA_PER_ROOT: usize = 16;
const MAX_FENCES: usize = 127;
const MAX_LIMIT: usize = 8192;
const MAX_CENSUS: usize = 65536;

fn refused(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::WouldBlock, message)
}
struct ProcessState {
    original: process::Identity,
    pending: usize,
    held: usize,
    held_sources: usize,
    held_outputs: usize,
    held_directories: usize,
    faulted: bool,
}
static PROCESS: OnceLock<Mutex<ProcessState>> = OnceLock::new();
static ORIGINAL_PID: AtomicU32 = AtomicU32::new(0);
// This rejection must precede any allocator, native identity I/O, OnceLock or
// copied mutex access after fork. A different process cannot reuse its parent's
// reservation. Exec creates a fresh image/coordinator and actual native census.
fn original_process() -> io::Result<u32> {
    // SAFETY: getpid is an async-signal-safe read of this actual process only.
    let actual = unsafe { libc::getpid() } as u32;
    let original = ORIGINAL_PID.load(Ordering::Acquire);
    if original != 0 && original != actual {
        return Err(io::Error::from_raw_os_error(libc::EPERM));
    }
    Ok(actual)
}
// Return only the process-local context. Each caller spells out its lock so
// lock-order analysis sees the acquisition and the guard's complete scope.
fn process_context() -> io::Result<(&'static Mutex<ProcessState>, process::Identity)> {
    let pid = original_process()?;
    match ORIGINAL_PID.compare_exchange(0, pid, Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => {}
        Err(original) if original == pid => {}
        Err(_) => return Err(io::Error::from_raw_os_error(libc::EPERM)),
    }
    let actual = process::read_identity(pid)?;
    let mutex = PROCESS.get_or_init(|| {
        Mutex::new(ProcessState {
            original: actual,
            pending: 0,
            held: 0,
            held_sources: 0,
            held_outputs: 0,
            held_directories: 0,
            faulted: false,
        })
    });
    Ok((mutex, actual))
}
fn check_process_state(state: &ProcessState, actual: process::Identity) -> io::Result<()> {
    if state.faulted {
        return Err(refused("native descriptor coordinator has an unresolved charge"));
    }
    if state.original.pid != actual.pid
        || state.original.birth != actual.birth
        || state.original.unique_id != actual.unique_id
        || state.original.exec_version != actual.exec_version
    {
        return Err(refused("descriptor coordinator belongs to another original process/image"));
    }
    Ok(())
}
fn limits() -> io::Result<libc::rlimit> {
    let mut limits = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    // SAFETY: valid resource and one sized writable native output.
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limits.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { limits.assume_init() })
}
fn kernel_max(fallback: libc::rlim_t) -> io::Result<libc::rlim_t> {
    #[cfg(target_os = "macos")]
    {
        let mut count: libc::c_int = 0;
        let mut size = std::mem::size_of_val(&count);
        // SAFETY: fixed read-only native key and correctly sized output.
        if unsafe {
            libc::sysctlbyname(
                c"kern.maxfilesperproc".as_ptr(),
                std::ptr::from_mut(&mut count).cast(),
                &mut size,
                std::ptr::null_mut(),
                0,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        if size != std::mem::size_of_val(&count) || count <= 0 {
            return Err(refused("native kernel descriptor ceiling is unknown"));
        }
        Ok((count as libc::rlim_t).min(fallback))
    }
    #[cfg(target_os = "linux")]
    {
        Ok(fallback)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = fallback;
        Err(io::ErrorKind::Unsupported.into())
    }
}
fn occupied() -> io::Result<usize> {
    #[cfg(target_os = "macos")]
    {
        let width = std::mem::size_of::<libc::proc_fdinfo>();
        // SAFETY: observe this actual process; the zero-size query supplies no output.
        let wanted = unsafe {
            libc::proc_pidinfo(
                std::process::id() as i32,
                libc::PROC_PIDLISTFDS,
                0,
                std::ptr::null_mut(),
                0,
            )
        };
        if wanted <= 0 || !(wanted as usize).is_multiple_of(width) {
            return Err(refused("original native descriptor census unavailable"));
        }
        let bytes = (wanted as usize)
            .checked_add(64 * width)
            .filter(|n| *n <= MAX_CENSUS * width)
            .ok_or_else(|| refused("native descriptor census exceeds bound"))?;
        let mut buffer = vec![0u8; bytes];
        // SAFETY: this owned byte buffer is writable for exactly bytes; no
        // kernel handle or authority is reconstructed from its observations.
        let got = unsafe {
            libc::proc_pidinfo(
                std::process::id() as i32,
                libc::PROC_PIDLISTFDS,
                0,
                buffer.as_mut_ptr().cast(),
                i32::try_from(bytes)
                    .map_err(|_| refused("native descriptor census size overflow"))?,
            )
        };
        if got <= 0 || got as usize >= bytes || !(got as usize).is_multiple_of(width) {
            return Err(refused("original native descriptor census is incomplete"));
        }
        Ok(got as usize / width)
    }
    #[cfg(target_os = "linux")]
    {
        // Native procfs is an explicit platform input, not source/SDK authority.
        // The listing itself is conservatively included in actual occupancy.
        let directory = std::fs::File::open("/proc/self/fd")?;
        use ::std::os::fd::AsRawFd as _;
        let mut fs = std::mem::MaybeUninit::<libc::statfs>::uninit();
        if unsafe { libc::fstatfs(directory.as_raw_fd(), fs.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if unsafe { fs.assume_init() }.f_type != 0x9fa0 {
            return Err(refused("descriptor census is not native procfs"));
        }
        let mut count = 1usize;
        for entry in std::fs::read_dir("/proc/self/fd")? {
            let name = entry?.file_name();
            if name.is_empty() || !name.as_encoded_bytes().iter().all(u8::is_ascii_digit) {
                return Err(refused("native descriptor census has an unknown entry"));
            }
            count = count
                .checked_add(1)
                .filter(|n| *n <= MAX_CENSUS)
                .ok_or_else(|| refused("native descriptor census exceeds bound"))?;
        }
        Ok(count)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        Err(io::ErrorKind::Unsupported.into())
    }
}
fn available(state: &ProcessState) -> io::Result<usize> {
    let limit = limits()?;
    let ceiling = usize::try_from(kernel_max(limit.rlim_cur)?)
        .map_err(|_| refused("native descriptor limit exceeds supported arithmetic"))?;
    let used = occupied()?
        .checked_add(state.pending)
        .and_then(|n| n.checked_add(RESERVE))
        .ok_or_else(|| refused("native descriptor demand overflow"))?;
    Ok(ceiling.saturating_sub(used))
}
fn acquire_limit(wanted: usize, minimum: usize) -> io::Result<()> {
    let mut before = limits()?;
    let hard = usize::try_from(kernel_max(before.rlim_max)?).unwrap_or(usize::MAX);
    if minimum > hard || minimum > MAX_LIMIT {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "native descriptor profile exceeds original hard/platform ceiling",
        ));
    }
    let target = wanted.min(hard).min(MAX_LIMIT);
    if target < minimum {
        return Err(refused("native descriptor profile cannot cover its minimum demand"));
    }
    if before.rlim_cur < target as libc::rlim_t {
        before.rlim_cur = target as libc::rlim_t;
        // SAFETY: explicit paid profile preparation changes only this process's
        // soft limit, never beyond the original hard/kernel bound.
        if unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &before) } != 0 {
            return Err(io::Error::last_os_error());
        }
    }
    let after = limits()?;
    if after.rlim_max != before.rlim_max || after.rlim_cur < minimum as libc::rlim_t {
        return Err(refused("native descriptor limit acquisition did not cover original demand"));
    }
    Ok(())
}

/// Native measured process-table/limit data, never capacity or execution authority.
#[derive(Clone, Debug)]
pub struct DescriptorObservation {
    /// Actual original process identity read from the kernel.
    pub process: process::Identity,
    /// Actual current soft limit.
    pub soft: u64,
    /// Actual current hard limit.
    pub hard: u64,
    /// Actual observed open process descriptions.
    pub occupied: usize,
    /// Reserved future descriptions not yet materialized.
    pub pending: usize,
    /// Materialized shared target charges, counted once per original owner.
    pub held_targets: usize,
    /// Materialized shared package files, charged once per original package.
    pub held_sources: usize,
    /// Actual original selected output descriptions, shared across consumers.
    pub held_outputs: usize,
    /// Original mutable directory identity/parent descriptions. No contents or permissions grant.
    pub held_directories: usize,
}
fn observation(state: &ProcessState) -> io::Result<DescriptorObservation> {
    let current = limits()?;
    #[allow(
        clippy::unnecessary_cast,
        reason = "libc rlim_t is 32-bit on some Unix targets; public observations use u64"
    )]
    let (soft, hard) = (current.rlim_cur as u64, current.rlim_max as u64);
    Ok(DescriptorObservation {
        process: state.original,
        soft,
        hard,
        occupied: occupied()?,
        pending: state.pending,
        held_targets: state.held,
        held_sources: state.held_sources,
        held_outputs: state.held_outputs,
        held_directories: state.held_directories,
    })
}
/// Actual observed acquisition phases for one shared input owner, data only.
#[derive(Clone, Debug)]
pub struct SharedAdmissionObservation {
    /// Before the explicit paid profile requested any limit change.
    pub before: DescriptorObservation,
    /// After checked limit acquisition and the scoped future reservation.
    pub reserved: DescriptorObservation,
    /// After original files are held and the same charge is materialized.
    pub materialized: DescriptorObservation,
    /// Demand derived from the same live original-directory plan.
    pub shared_descriptors: usize,
}

/// Existing target observation vocabulary retained as DATA compatibility.
pub type TargetAdmissionObservation = SharedAdmissionObservation;
/// Native package acquisition observations, not source or execution authority.
pub type SourceAdmissionObservation = SharedAdmissionObservation;

/// One process-local budget used by original paid Host/Root preparation and its
/// later member permits. All instances coordinate the SAME real process table.
pub struct DescriptorBudget {
    active: AtomicUsize,
    limit: usize,
    per_root: usize,
    // Retain every selected package for this actual graph. Sources do not own
    // this budget, avoiding an Arc cycle; failed captures cannot refresh here.
    sources: Mutex<SourceEntries>,
}
type SourceEntries = BTreeMap<PathBuf, Result<Arc<AdmittedPackageSource>, String>>;

/// One real invocation's immutable selected package namespace population.
/// This is only a registry lifetime boundary: capacity still comes from the
/// SAME original native budget/process ledger. A long-lived Host must not keep
/// every past Job's package paths/failures in its process-wide default registry.
pub struct SourceScope {
    // Original package owners close before the shared budget reference drops.
    sources: Mutex<SourceEntries>,
    budget: Arc<DescriptorBudget>,
}
impl SourceScope {
    pub fn capture(
        &self,
        root: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedPackageSource>> {
        self.budget.capture_source_from(&self.sources, root, deadline)
    }
}
/// Scoped per-member capacity. Retain through the original owning retirement.
pub struct RootPermit {
    budget: Arc<DescriptorBudget>,
    _reservation: Option<Reservation>,
}
impl RootPermit {
    /// Release only the active-member slot while retaining the SAME complete
    /// descriptor envelope with retired original handles.
    /// # Safety
    /// The actual owning native operation has positively closed its target,
    /// helper and physical streams. No status/JSON/FD observation substitutes
    /// for that owner; unknown/incomplete operations must retain RootPermit.
    /// This transitions FD accounting only, never CPU or hosted retirement.
    pub unsafe fn into_retained(mut self) -> OriginalInputPermit {
        let Some(reservation) = self._reservation.take() else { std::process::abort() };
        OriginalInputPermit { _reservation: reservation, _budget: self.budget.clone() }
    }
}
/// Explicit future original-input/transport envelope in the SAME paid process
/// budget. This consumes no compiler-active slot, CPU, SDK or execution grant.
/// The native caller holds it LAST until every actual original/transient FD
/// in that envelope has closed, including failed delivery/materialization.
pub struct OriginalInputPermit {
    _reservation: Reservation,
    _budget: Arc<DescriptorBudget>,
}
struct Reservation {
    count: usize,
    materialized: Option<SharedKind>,
}
#[derive(Clone, Copy)]
enum SharedKind {
    Target,
    Source,
    Output,
    Directory,
}
impl Reservation {
    fn materialized(&mut self, kind: SharedKind) -> io::Result<()> {
        self.materialized_count(kind, self.count)
    }
    fn materialized_count(&mut self, kind: SharedKind, count: usize) -> io::Result<()> {
        if self.materialized.is_some() || count > self.count {
            return Err(refused("native materialized descriptor charge is inconsistent"));
        }
        let (process_coordinator, actual) = process_context()?;
        let mut state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        let pending = state
            .pending
            .checked_sub(self.count)
            .ok_or_else(|| refused("descriptor pending charge was lost"))?;
        let charge = match kind {
            SharedKind::Target => &mut state.held,
            SharedKind::Source => &mut state.held_sources,
            SharedKind::Output => &mut state.held_outputs,
            SharedKind::Directory => &mut state.held_directories,
        };
        *charge =
            charge.checked_add(count).ok_or_else(|| refused("descriptor held charge overflow"))?;
        state.pending = pending;
        self.count = count;
        self.materialized = Some(kind);
        Ok(())
    }
}
impl Drop for Reservation {
    fn drop(&mut self) {
        let Ok((process_coordinator, actual)) = process_context() else {
            return;
        };
        if let Ok(mut state) = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))
        {
            if check_process_state(&state, actual).is_err() {
                return;
            }
            let charge = match self.materialized {
                Some(SharedKind::Target) => &mut state.held,
                Some(SharedKind::Source) => &mut state.held_sources,
                Some(SharedKind::Output) => &mut state.held_outputs,
                Some(SharedKind::Directory) => &mut state.held_directories,
                None => &mut state.pending,
            };
            // An impossible ledger transition poisons future admission rather
            // than making unknown or still-live capacity available.
            if let Some(remaining) = charge.checked_sub(self.count) {
                *charge = remaining;
            } else {
                state.faulted = true;
            }
        }
    }
}
impl Drop for RootPermit {
    fn drop(&mut self) {
        self.budget.active.fetch_sub(1, Ordering::AcqRel);
    }
}

/// Actual held target originals FIRST, admission charge LAST. Arc sharing and
/// failed-command retention keep this same charge until all target files close.
/// No constructor accepts saved manifests or a numeric success report.
pub struct AdmittedTargetSysroot {
    inputs: HeldRustTargetSysroot,
    _reservation: Reservation,
    _budget: Arc<DescriptorBudget>,
    observation: TargetAdmissionObservation,
}
impl AdmittedTargetSysroot {
    /// Actual acquisition observations, not a replayable reservation or SDK verdict.
    pub fn admission_observation(&self) -> &TargetAdmissionObservation {
        &self.observation
    }
    /// Reserve later member preparation through this SAME original budget.
    pub fn try_member(&self) -> io::Result<Option<RootPermit>> {
        self._budget.try_root()
    }
    /// Charge the real Host control anchor and complete child copy population
    /// through the SAME admitted target/Host budget before any socket or dup.
    pub fn reserve_member_control(&self) -> io::Result<OriginalInputPermit> {
        self._budget
            .reserve_original_inputs(trust_resource_provenance::ORIGINAL_CONTROL_DESCRIPTORS + 1)
    }
    /// Reserve the complete parked-primary pair plus its control transfer
    /// through this SAME process coordinator. This consumes no active member
    /// slot, RootPermit or CPU credit.
    ///
    /// # Errors
    /// Refuses if the original process or descriptor capacity is unavailable.
    pub fn reserve_paired_control(&self) -> io::Result<OriginalInputPermit> {
        let demand = self._budget.per_root
            .checked_add(trust_resource_provenance::ORIGINAL_CONTROL_DESCRIPTORS + 1)
            .ok_or_else(|| refused("paired descriptor envelope overflow"))?;
        self._budget.reserve_original_inputs(demand)
    }
    /// Recheck the same original target and compiler inputs.
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        original_process()?;
        self.inputs.validate(deadline)
    }
    /// Bind actual finalized compiler arguments and effective environment.
    pub fn validate_invocation(
        &self,
        compiler: &Arc<HeldProgram>,
        program: &[u8],
        arg0: Option<&[u8]>,
        args: &[Vec<u8>],
        environment: &[(Vec<u8>, Vec<u8>)],
        deadline: Instant,
    ) -> io::Result<()> {
        original_process()?;
        self.inputs.validate_invocation(compiler, program, arg0, args, environment, deadline)
    }
    /// Captured byte observations only, never current validity/SDK authority.
    pub fn file_observations(&self) -> impl Iterator<Item = &FileObservation> {
        self.inputs.file_observations()
    }
    /// Complete selected target namespace DATA from SAME admitted originals.
    /// Other files beneath the SDK root are not included by root membership.
    pub fn selected_directory(&self, deadline: Instant) -> io::Result<PathBuf> {
        original_process()?;
        self.inputs.selected_directory(deadline)
    }
}
/// Actual original package inputs first, scoped native charge last. The same
/// graph budget retains this owner, and command/failure Arcs may outlive it.
/// No report, digest or caller Boolean creates this owner or makes work eligible.
pub struct AdmittedPackageSource {
    inputs: HeldPackageSource,
    observation: SourceAdmissionObservation,
    _reservation: Reservation,
}

/// Original selected output DATA first, SAME native charge last. The parent
/// graph retains/shares this Arc for a real retired producer's typed OutputFile;
/// it separately binds SDK/source, excludes writers and validates consumers.
/// Root membership and this owner alone establish no eligibility or proof.
pub struct AdmittedRootFile {
    inputs: HeldRootFile,
    observation: SharedAdmissionObservation,
    _reservation: Reservation,
    _budget: Arc<DescriptorBudget>,
}

/// Retained mutable directory identity and SAME descriptor-budget charge.
/// This grants neither complete namespace contents nor write/SDK authority.
pub struct AdmittedDirectory {
    inputs: HeldDirectoryInput,
    _reservation: Reservation,
    _budget: Arc<DescriptorBudget>,
}
/// Directory/ancestor originals derived only from the SAME held output root.
/// The parent selects a real Unit namespace and separately excludes writers;
/// this capture itself grants no writes, producer eligibility or execution.
pub struct AdmittedRootDirectory {
    inputs: HeldRootDirectory,
    _reservation: Reservation,
    _budget: Arc<DescriptorBudget>,
}
/// Selected output root derived through the actual original master FD chain.
/// The complete native charge remains after the root closes. This is input
/// custody only; real Layout/producer/Host writer owners remain separate.
pub struct AdmittedOutputRoot {
    inputs: Arc<HeldOutputRoot>,
    _budget: Arc<DescriptorBudget>,
}
impl AdmittedOutputRoot {
    pub fn original(&self) -> &Arc<HeldOutputRoot> {
        &self.inputs
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        original_process()?;
        self.inputs.validate(deadline)
    }
}
impl AdmittedRootDirectory {
    pub fn require_disjoint_trees(
        &self,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<()> {
        original_process()?;
        self.inputs.require_disjoint_trees(exclusions, deadline)
    }
    pub fn path(&self) -> &Path {
        self.inputs.path()
    }
    pub fn output_root(&self) -> &Path {
        self.inputs.output_root()
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        original_process()?;
        self.inputs.validate(deadline)
    }
    pub fn descriptor(&self, deadline: Instant) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        original_process()?;
        self.inputs.descriptor(deadline)
    }
}
impl AdmittedDirectory {
    pub fn original_tree_identities(&self, deadline: Instant) -> io::Result<Vec<(u64, u64)>> {
        original_process()?;
        self.inputs.original_tree_identities(deadline)
    }
    /// Borrow the SAME admitted original directory. Callers retain this owner
    /// and separately admit their exact read/write operation and FD copies.
    pub fn descriptor(&self, deadline: Instant) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        original_process()?;
        self.inputs.descriptor(deadline)
    }
    pub fn original_identity(&self, deadline: Instant) -> io::Result<FileIdentity> {
        original_process()?;
        let (device, inode) = self.inputs.original_identity(deadline)?;
        Ok(FileIdentity { device, inode })
    }
    pub fn path(&self) -> &Path {
        self.inputs.path()
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        original_process()?;
        self.inputs.validate(deadline)
    }
}
impl AdmittedRootFile {
    /// Owned captured metadata plus this Arc allocation. Shared original
    /// selected-root/budget owners are counted by their graph, not again here.
    pub fn retained_bytes(&self) -> Option<usize> {
        self.inputs
            .retained_bytes()?
            .checked_add(
                std::mem::size_of::<Self>().checked_sub(std::mem::size_of::<HeldRootFile>())?,
            )?
            .checked_add(2 * std::mem::size_of::<usize>())
    }
    pub fn observation(&self) -> &FileObservation {
        self.inputs.observation()
    }
    pub fn output_root(&self) -> &Path {
        self.inputs.output_root()
    }
    pub fn admission_observation(&self) -> &SharedAdmissionObservation {
        &self.observation
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        original_process()?;
        self.inputs.validate(deadline)
    }
    pub fn descriptor(&self, deadline: Instant) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        original_process()?;
        self.inputs.descriptor(deadline)
    }
}
impl std::fmt::Debug for AdmittedPackageSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalPackageInputs").field("path", &self.path()).finish_non_exhaustive()
    }
}
impl AdmittedPackageSource {
    pub fn original_root_identity(&self, deadline: Instant) -> io::Result<FileIdentity> {
        original_process()?;
        let (device, inode) = self.inputs.original_root_identity(deadline)?;
        Ok(FileIdentity { device, inode })
    }
    pub fn path(&self) -> &Path {
        self.inputs.path()
    }
    pub fn content_digest(&self) -> &[u8; 32] {
        self.inputs.content_digest()
    }
    pub fn entries(&self) -> &[PackageEntry] {
        self.inputs.entries()
    }
    pub fn admission_observation(&self) -> &SourceAdmissionObservation {
        &self.observation
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        original_process()?;
        self.inputs.validate(deadline)
    }
    pub fn read(&self, relative: &Path, deadline: Instant) -> io::Result<Vec<u8>> {
        original_process()?;
        self.inputs.read(relative, deadline)
    }
}

impl DescriptorBudget {
    pub(crate) fn verify_local_file(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        original: &AdmittedRootFile,
        deadline: Instant,
    ) -> io::Result<()> {
        original_process()?;
        if !Arc::ptr_eq(self, &original._budget) || !original.inputs.belongs_to_root(output) {
            return Err(refused("local file is not from SAME original output/budget"));
        }
        original.validate(deadline)
    }
    pub(crate) fn verify_local_directory(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        original: &AdmittedRootDirectory,
        deadline: Instant,
    ) -> io::Result<()> {
        original_process()?;
        if !Arc::ptr_eq(self, &original._budget) || !original.inputs.belongs_to_root(output) {
            return Err(refused("local directory is not from SAME original output/budget"));
        }
        original.validate(deadline)
    }
    /// Backend of the fixed opaque LocalIoScope. Caller must hold actual
    /// native second-unit admission and independent writer exclusion through
    /// every IO handle's closure; this backend is not a public path-copy API.
    pub(crate) unsafe fn publish_local_file(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        source: &AdmittedRootFile,
        destination: &Path,
        publication: ([u8; 16], u64),
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootFile>> {
        let (operation, ordinal) = publication;
        let (mut reservation, before, reserved) =
            self.reserve_shared(HeldRootFile::publication_descriptor_bound())?;
        self.verify_local_file(output, source, deadline)?;
        // SAFETY: only LocalIoScope calls this after actual native local
        // admission; originals/CPU/exclusion outlive all synchronous IO here.
        let inputs = unsafe {
            output.publish_original_file(
                &source.inputs,
                destination,
                operation,
                ordinal,
                exclusions,
                deadline,
            )?
        };
        reservation.materialized_count(SharedKind::Output, inputs.descriptor_count())?;
        let materialized = {
            let (process_coordinator, actual) = process_context()?;
            let state = process_coordinator
                .lock()
                .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
            check_process_state(&state, actual)?;
            observation(&state)?
        };
        Ok(Arc::new(AdmittedRootFile {
            inputs,
            observation: SharedAdmissionObservation {
                before,
                reserved,
                materialized,
                shared_descriptors: reservation.count,
            },
            _reservation: reservation,
            _budget: Arc::clone(self),
        }))
    }
    /// Existing declared compilation root, selected from the SAME master
    /// original. Capacity precedes traversal and the extra retained root FD.
    pub fn capture_output_root(
        self: &Arc<Self>,
        master: &HeldOutputRoot,
        path: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedOutputRoot>> {
        self.admit_selected_root(master, path, None, deadline)
    }
    /// Create a NEW declared root under SAME originals, vetoing actual
    /// protected SDK/source trees before every mkdir. Existing final refuses.
    pub fn prepare_output_root(
        self: &Arc<Self>,
        master: &HeldOutputRoot,
        path: &Path,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedOutputRoot>> {
        self.admit_selected_root(master, path, Some(exclusions), deadline)
    }
    fn admit_selected_root(
        self: &Arc<Self>,
        master: &HeldOutputRoot,
        path: &Path,
        prepare: Option<&PublicationExclusions>,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedOutputRoot>> {
        original_process()?;
        let count = HeldRootDirectory::capture_descriptor_bound()
            .checked_add(1)
            .ok_or_else(|| refused("selected root descriptor envelope overflow"))?;
        let (mut reservation, _, _) = self.reserve_shared(count)?;
        let directory = match prepare {
            Some(exclusions) => master.prepare_directory_excluding(path, exclusions, deadline)?,
            None => master.directory(path, deadline)?,
        };
        let output = HeldOutputRoot::from_original_directory(directory, deadline)?;
        reservation.materialized_count(SharedKind::Directory, output.descriptor_count())?;
        let guard =
            Arc::new(OriginalInputPermit { _reservation: reservation, _budget: Arc::clone(self) });
        let inputs = Arc::new(output.retain_descriptor_guard(guard)?);
        Ok(Arc::new(AdmittedOutputRoot { inputs, _budget: Arc::clone(self) }))
    }
    /// Capture existing selected namespace originals below the SAME root.
    /// Data/path membership cannot establish Unit or writer eligibility.
    pub fn capture_output_directory(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        path: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootDirectory>> {
        self.admit_output_directory(output, path, false, None, deadline)
    }
    /// Import an actual received original, never a saved directory record.
    /// The receiver must pay its SCM population BEFORE receiving, then retain
    /// this same budget-backed owner through every actual consumer/failure.
    pub fn capture_output_directory_from_original(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        path: &Path,
        original: std::os::fd::OwnedFd,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootDirectory>> {
        self.admit_output_directory(output, path, false, Some(original), deadline)
    }
    /// Parent preparation creates a NEW final namespace through original root
    /// FDs, never create_dir_all on projected paths. Admit BEFORE every mkdir
    /// or open; a failed preparation leaves created input/evidence intact.
    pub fn prepare_output_directory(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        path: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootDirectory>> {
        self.admit_output_directory(output, path, true, None, deadline)
    }
    pub(crate) fn prepare_local_directory(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        path: &Path,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootDirectory>> {
        original_process()?;
        let (mut reservation, _, _) =
            self.reserve_shared(HeldRootDirectory::capture_descriptor_bound())?;
        output.require_disjoint_trees(exclusions, deadline)?;
        let inputs = output.prepare_directory_excluding(path, exclusions, deadline)?;
        reservation.materialized_count(SharedKind::Directory, inputs.descriptor_count())?;
        Ok(Arc::new(AdmittedRootDirectory {
            inputs,
            _reservation: reservation,
            _budget: Arc::clone(self),
        }))
    }
    fn admit_output_directory(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        path: &Path,
        create: bool,
        original: Option<std::os::fd::OwnedFd>,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootDirectory>> {
        original_process()?;
        let (mut reservation, _, _) =
            self.reserve_shared(HeldRootDirectory::capture_descriptor_bound())?;
        let inputs = if let Some(original) = original {
            output.directory_from_original(path, std::fs::File::from(original), deadline)?
        } else if create {
            output.prepare_directory(path, deadline)?
        } else {
            output.directory(path, deadline)?
        };
        reservation.materialized_count(SharedKind::Directory, inputs.descriptor_count())?;
        Ok(Arc::new(AdmittedRootDirectory {
            inputs,
            _reservation: reservation,
            _budget: Arc::clone(self),
        }))
    }
    /// Actual mutable directory/ancestor originals for native input/policy
    /// preparation. Admission precedes every capture description; a pathname
    /// or the returned identity alone grants no writes or resource execution.
    pub fn capture_directory(
        self: &Arc<Self>,
        path: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedDirectory>> {
        original_process()?;
        let (mut reservation, _, _) =
            self.reserve_shared(HeldDirectoryInput::capture_descriptor_bound())?;
        let inputs = HeldDirectoryInput::open(path, deadline)?;
        reservation.materialized_count(SharedKind::Directory, inputs.descriptor_count())?;
        Ok(Arc::new(AdmittedDirectory {
            inputs,
            _reservation: reservation,
            _budget: Arc::clone(self),
        }))
    }
    /// One caller-retained invocation registry, not a new admission controller.
    /// Keep it through all of that Job's inputs, consumers and failed outcomes;
    /// creating another scope cannot settle or clear any earlier scope/owner.
    pub fn source_scope(self: &Arc<Self>) -> io::Result<Arc<SourceScope>> {
        original_process()?;
        Ok(Arc::new(SourceScope { sources: Mutex::new(BTreeMap::new()), budget: Arc::clone(self) }))
    }
    /// Capture only the parent's independently selected real Unit OutputFile
    /// after its actual producing member has retired. This owns DATA only; a
    /// saved receipt/status/hash cannot discharge those caller prerequisites.
    /// Admission precedes opening ANY new capture descriptions, and unused
    /// envelope room returns only after the actual file and parent population
    /// has materialized. Share the returned Arc across its real consumers.
    pub fn capture_output_file(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        selected: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootFile>> {
        self.admit_output_file(output, selected, None, deadline)
    }
    /// Import the actual retired producer's read-only data FD. Root-relative
    /// native traversal and current original bytes are checked independently;
    /// no receipt/digest supplies producer eligibility or FD authority.
    pub fn capture_output_file_from_original(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        selected: &Path,
        original: std::os::fd::OwnedFd,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootFile>> {
        self.admit_output_file(output, selected, Some(original), deadline)
    }
    fn admit_output_file(
        self: &Arc<Self>,
        output: &HeldOutputRoot,
        selected: &Path,
        original: Option<std::os::fd::OwnedFd>,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedRootFile>> {
        original_process()?;
        let (mut reservation, before, reserved) =
            self.reserve_shared(HeldRootFile::capture_descriptor_bound())?;
        let inputs = if let Some(original) = original {
            output.file_from_original(selected, std::fs::File::from(original), deadline)?
        } else {
            output.file(selected, deadline)?
        };
        reservation.materialized_count(SharedKind::Output, inputs.descriptor_count())?;
        let materialized = {
            let (process_coordinator, actual) = process_context()?;
            let state = process_coordinator
                .lock()
                .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
            check_process_state(&state, actual)?;
            observation(&state)?
        };
        Ok(Arc::new(AdmittedRootFile {
            inputs,
            observation: SharedAdmissionObservation {
                before,
                reserved,
                materialized,
                shared_descriptors: reservation.count,
            },
            _reservation: reservation,
            _budget: Arc::clone(self),
        }))
    }
    /// Explicit native preparation for the existing compiler-root profile.
    /// Acquisition is checked, bounded by original hard/kernel limits.
    pub fn prepare(roots: usize) -> io::Result<()> {
        let (process_coordinator, actual) = process_context()?;
        let state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        let wanted = RESERVE
            .saturating_add(roots.saturating_mul(2 * MAX_FENCES + EXTRA_PER_ROOT))
            .clamp(1024, MAX_LIMIT);
        // Existing root parallelism may shrink at a hard ceiling; at least one
        // actual per-root envelope must still fit in new()/try_root().
        acquire_limit(wanted, 0)
    }
    /// Create the ONE caller-owned preparation coordinator before the live
    /// target plan is materialized. This grants no slots and never raises a
    /// limit; capture_target/try_root perform actual checked admission.
    pub fn for_preparation(roots: usize, fences: usize) -> io::Result<Arc<Self>> {
        let (process_coordinator, actual) = process_context()?;
        let state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        let per_root = fences
            .checked_mul(2)
            .and_then(|n| n.checked_add(EXTRA_PER_ROOT))
            .ok_or_else(|| refused("native member descriptor envelope overflow"))?;
        if roots == 0 || roots > MAX_CENSUS {
            return Err(refused("native descriptor profile has unsupported worker bound"));
        }
        // The policy snapshot is complete. Allocation constructs an independent
        // budget; every later reservation rechecks the same process coordinator.
        drop(state);
        Ok(Arc::new(Self {
            active: AtomicUsize::new(0),
            limit: roots,
            per_root,
            sources: Mutex::new(BTreeMap::new()),
        }))
    }
    /// Per-budget policy ceiling; not current availability or a grant.
    pub fn member_limit(&self) -> usize {
        self.limit
    }
    /// Observe actual available process room; no constructor silently raises it.
    pub fn new(roots: usize, fences: usize) -> io::Result<Arc<Self>> {
        let (process_coordinator, actual) = process_context()?;
        let state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        let per_root = fences
            .checked_mul(2)
            .and_then(|n| n.checked_add(EXTRA_PER_ROOT))
            .ok_or_else(|| refused("native member descriptor envelope overflow"))?;
        let limit = roots.min(available(&state)? / per_root);
        if limit == 0 {
            return Err(refused(
                "native admission lacks descriptors for one retained compiler root",
            ));
        }
        // The policy snapshot is complete. Allocation constructs an independent
        // budget; every later reservation rechecks the same process coordinator.
        drop(state);
        Ok(Arc::new(Self {
            active: AtomicUsize::new(0),
            limit,
            per_root,
            sources: Mutex::new(BTreeMap::new()),
        }))
    }
    /// Perform actual shared target admission from a live original-directory
    /// plan during paid SDK/Root preparation, then materialize the original FDs.
    /// The SAME budget is retained and later supplies member RootPermits.
    pub fn capture_target(
        self: &Arc<Self>,
        plan: RustTargetSysrootPlan,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedTargetSysroot>> {
        self.capture_target_after_reservation(plan, deadline, || {})
    }
    // Production has no hook. Native controls create real post-reservation FD
    // pressure/mutation here; a callback result never replaces materialization.
    fn capture_target_after_reservation(
        self: &Arc<Self>,
        plan: RustTargetSysrootPlan,
        deadline: Instant,
        after_reserved: impl FnOnce(),
    ) -> io::Result<Arc<AdmittedTargetSysroot>> {
        original_process()?;
        let count = plan.descriptor_demand(deadline)?;
        let (mut reservation, before, reserved) = self.reserve_shared(count)?;
        after_reserved();
        let inputs = plan.materialize(deadline)?;
        reservation.materialized(SharedKind::Target)?;
        let materialized = {
            let (process_coordinator, actual) = process_context()?;
            let state = process_coordinator
                .lock()
                .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
            check_process_state(&state, actual)?;
            observation(&state)?
        };
        Ok(Arc::new(AdmittedTargetSysroot {
            inputs,
            _reservation: reservation,
            _budget: self.clone(),
            observation: TargetAdmissionObservation {
                before,
                reserved,
                materialized,
                shared_descriptors: count,
            },
        }))
    }
    fn reserve_shared(
        &self,
        count: usize,
    ) -> io::Result<(Reservation, DescriptorObservation, DescriptorObservation)> {
        let (process_coordinator, actual) = process_context()?;
        let mut state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        let before = observation(&state)?;
        let overhead = before
            .occupied
            .checked_add(state.pending)
            .and_then(|n| n.checked_add(RESERVE))
            .ok_or_else(|| refused("native shared input descriptor demand overflow"))?;
        let minimum = overhead
            .checked_add(count)
            .and_then(|n| n.checked_add(self.per_root))
            .ok_or_else(|| refused("native shared input descriptor demand overflow"))?;
        let wanted = overhead
            .checked_add(count)
            .and_then(|n| n.checked_add(self.limit.saturating_mul(self.per_root)))
            .ok_or_else(|| refused("native shared input descriptor demand overflow"))?;
        acquire_limit(wanted.max(1024), minimum)?;
        if available(&state)?
            < count
                .checked_add(self.per_root)
                .ok_or_else(|| refused("native shared input descriptor demand overflow"))?
        {
            return Err(refused("native shared input reservation unavailable"));
        }
        state.pending = state
            .pending
            .checked_add(count)
            .ok_or_else(|| refused("native descriptor pending overflow"))?;
        let reserved = match observation(&state) {
            Ok(observed) => observed,
            Err(error) => {
                // No materialization or delivery has started. Return exactly
                // this future charge under the SAME lock before returning.
                state.pending -= count;
                return Err(error);
            }
        };
        drop(state);
        Ok((Reservation { count, materialized: None }, before, reserved))
    }
    /// Explicit checked capacity acquisition before receiving or constructing
    /// a known native original-input envelope. The future charge remains
    /// pending through its actual lifetime, conservatively separate from the
    /// current kernel census, just like a member RootPermit's envelope.
    /// Numbers describe demand only; they prove no original-FD ownership.
    pub fn reserve_original_inputs(
        self: &Arc<Self>,
        count: usize,
    ) -> io::Result<OriginalInputPermit> {
        if count == 0 || count > MAX_LIMIT {
            return Err(refused("original input descriptor envelope exceeds bound"));
        }
        let (reservation, _, _) = self.reserve_shared(count)?;
        Ok(OriginalInputPermit { _reservation: reservation, _budget: Arc::clone(self) })
    }
    /// SAME existing compiler transport envelope without consuming a scheduler
    /// active-root slot. The actual parent-bank primary separately bounds CPU
    /// execution, and this permit outlives all corresponding original handles.
    pub fn reserve_member_transport(self: &Arc<Self>) -> io::Result<OriginalInputPermit> {
        self.reserve_original_inputs(self.per_root)
    }
    /// Capture once per selected package in this SAME actual paid graph. The
    /// original descriptor-relative plan and materialization run under the
    /// existing process-wide reservation, not a second source capacity pool.
    pub fn capture_source(
        self: &Arc<Self>,
        root: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedPackageSource>> {
        self.capture_source_from(&self.sources, root, deadline)
    }
    fn capture_source_from(
        self: &Arc<Self>,
        registry: &Mutex<SourceEntries>,
        root: &Path,
        deadline: Instant,
    ) -> io::Result<Arc<AdmittedPackageSource>> {
        original_process()?;
        let mut sources =
            registry.lock().map_err(|_| refused("original package registry poisoned"))?;
        if let Some(original) = sources.get(root) {
            let original = original.as_ref().map_err(|error| io::Error::other(error.clone()))?;
            original.validate(deadline)?;
            return Ok(original.clone());
        }
        if sources.len() >= 4096 {
            return Err(refused("native graph package population exceeds bound"));
        }
        let result = (|| {
            let plan = PackageSourcePlan::capture(root, deadline)?;
            let count = plan.descriptor_demand(deadline)?;
            let (mut reservation, before, reserved) = self.reserve_shared(count)?;
            let inputs = plan.materialize(deadline)?;
            reservation.materialized(SharedKind::Source)?;
            let materialized = {
                let (process_coordinator, actual) = process_context()?;
                let state = process_coordinator
                    .lock()
                    .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
                check_process_state(&state, actual)?;
                observation(&state)?
            };
            Ok(Arc::new(AdmittedPackageSource {
                inputs,
                observation: TargetAdmissionObservation {
                    before,
                    reserved,
                    materialized,
                    shared_descriptors: count,
                },
                _reservation: reservation,
            }))
        })();
        match &result {
            Ok(original) => {
                sources.insert(root.into(), Ok(Arc::clone(original)));
            }
            Err(error) => {
                sources
                    .insert(root.into(), Err(format!("original package capture refused: {error}")));
            }
        }
        result
    }
    /// Acquire a real scoped member reservation without changing process limits.
    pub fn try_root(self: &Arc<Self>) -> io::Result<Option<RootPermit>> {
        let (process_coordinator, actual) = process_context()?;
        let mut state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        if self.active.load(Ordering::Acquire) >= self.limit || available(&state)? < self.per_root {
            return Ok(None);
        }
        state.pending = state
            .pending
            .checked_add(self.per_root)
            .ok_or_else(|| refused("native descriptor pending overflow"))?;
        self.active.fetch_add(1, Ordering::AcqRel);
        Ok(Some(RootPermit {
            budget: self.clone(),
            _reservation: Some(Reservation { count: self.per_root, materialized: None }),
        }))
    }
    /// Fresh actual process observations; unavailable remains an error.
    pub fn observation(&self) -> io::Result<DescriptorObservation> {
        let (process_coordinator, actual) = process_context()?;
        let state = process_coordinator
            .lock()
            .map_err(|_| refused("native descriptor coordinator is poisoned"))?;
        check_process_state(&state, actual)?;
        observation(&state)
    }
    /// True only when no member RootPermit is held by this budget.
    pub fn idle(&self) -> bool {
        self.active.load(Ordering::Acquire) == 0
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests;
