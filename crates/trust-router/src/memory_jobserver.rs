// trust-router/memory_jobserver.rs: cross-process memory-aware token bucket.
//
// The 2026-06-17 OOM kernel panics had two causes. A single uncapped solve is
// handled per-process by `MemoryGuard` (see memory_guard.rs). The SECOND cause —
// ~14 concurrent `trustc` workers each spawning `ay` with NO aggregate budget,
// summing to ~143 GB on a 36 GB host — is a CROSS-PROCESS problem no single
// process can see. This module is the missing aggregate budget: a memory-aware
// token bucket shared by participating workers that select the SAME token path,
// through a small file guarded by a stable, authority-checked OS advisory flock.
//
// It is NOT a daemon. There is no persistent server, no polling loop, and no
// syscall on the inner solver path. A worker ACQUIRES a byte reservation before
// same-owner solver work and RELEASES it (via RAII `Drop`) when that work finishes.
// The file guard remains owned by its recording PID; transferring ownership to an
// external child is not supported by this lane. The process keeps a conservative
// floor of effective host RAM (physical RAM capped by every cgroup limit visible
// through the current Linux cgroup mount). A configured coordinator FAILS CLOSED
// when its ledger is unavailable, malformed,
// untrusted, or remains full through the admission deadline: `acquire` returns an
// explicit error instead of launching an unaccounted solver and turning an
// integrity/availability fault into an OOM.
//
// DROP-IN: with no token file and no coordinator (a raw `trustc` invocation), the
// reservation is a no-op that always succeeds, so standalone verification behaves
// exactly as before. Once `TRUST_MEMORY_JOBSERVER` is explicitly configured it is
// authoritative, not an optional hint.
//
// AUTHORITY CONTRACT: the configured ledger must live below a pre-existing,
// euid-owned parent. The configured path must be absolute and already canonical:
// relative paths and lexical/symlink aliases are rejected so retries and Drop
// cannot silently move a reservation to another ledger. The canonical
// root-to-leaf directory chain is owned by the euid/root and never group/other
// writable. Lock and ledger leaves are private, euid-owned, regular, single-link
// files. Authority directories/leaves must not carry an extended ACL that grants
// another principal mutation: uid/mode/link checks are enforced here, while ACL
// semantics are part of the deployment filesystem TCB. Same-euid workers are the
// cooperating principals of one build. On Linux
// the stable lock also binds every participant to the same PID namespace before
// PID-based stale-row pruning is allowed. All participants must also share the
// same trusted mount/backing-filesystem view: an identical absolute spelling
// alone cannot prove that across separate mount namespaces. Linux `/proc` PID,
// cgroup, mountinfo, nsfs, and cgroupfs views are deployment TCB inputs; missing,
// unreadable, or malformed visible inputs fail closed, but a malicious/masked
// mount namespace is not authenticated here. The backing LOCAL Unix filesystem
// is part of the authority/availability TCB and must honor
// flock, create-new, hard-link, atomic same-directory rename, and fsync semantics.
// Synchronous filesystem calls are not preempted by the admission wait deadline;
// platforms/filesystems where these guarantees cannot be established must reject
// the configured file lane rather than weakening it.
//
// CRASH-SAFETY: a worker that dies mid-solve cannot run its `Drop`, so its
// reservation would leak. The token file therefore stores one `pid bytes ts` line
// per live reservation; every acquire/release first PRUNES lines whose PID is
// definitely no longer alive (`kill(pid, 0)`). Age alone is never enough: a
// legitimate long-running solver must remain counted. PID reuse may retain an old
// row conservatively, but it can never cause an undercount. The flock itself is
// released by the OS on crash (advisory flock semantics).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::hash_map::RandomState;
use std::fs::{File, OpenOptions};
use std::hash::{BuildHasher, Hash, Hasher};
use std::io::{Read, Write};
#[cfg(target_os = "linux")]
use std::io::{Seek, SeekFrom};
#[cfg(unix)]
use std::os::fd::AsRawFd;
#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[cfg(not(unix))]
use trust_cache::coordination::{self, CoordinationConfig};

/// Default fraction of effective RAM the selected coordinator domain is allowed
/// to reserve. Leaves headroom for the kernel, the trustc workers themselves, and
/// the OS page cache so that fully-subscribed reservations do not themselves
/// drive the machine into swap/OOM. Conservative by design (the OOM that
/// motivated this reserved ~4x physical RAM).
const DEFAULT_BUDGET_NUMERATOR: u64 = 70;
const DEFAULT_BUDGET_DENOMINATOR: u64 = 100;

/// Bounded best-effort release LOCK-WAIT window. Ledger edits normally hold the
/// lock only for a tiny read/write/fsync transaction; allowing brief contention
/// avoids a live process leaking its own row. The bound caps cooperative lock
/// contention, not synchronous local-filesystem calls. If it expires the row
/// stays counted until PID-death pruning (safe denial, never an undercount).
const RELEASE_LOCK_DEADLINE: Duration = Duration::from_secs(1);

/// Default deadline an over-budget [`acquire`] is allowed to BLOCK, waiting for
/// peers to release enough bytes to fit the request, before it fails the current
/// verification closed. This is the admission-control knob: while the budget is
/// full a new worker parks here instead of piling on, smoothing the participating
/// footprint. It bounds cooperative lock/capacity waiting; synchronous filesystem
/// I/O remains in the local-filesystem availability TCB. Expiry never authorizes
/// an unaccounted solver. Overridable per-process via
/// `TRUST_MEMORY_JOBSERVER_DEADLINE_MS` (no new CLI flag; env mirrors the
/// existing `TRUST_MEMORY_JOBSERVER` knob).
const DEFAULT_ACQUIRE_DEADLINE: Duration = Duration::from_secs(120);

/// Env override for [`DEFAULT_ACQUIRE_DEADLINE`], in milliseconds. `0` disables
/// blocking entirely (acquire is grant-or-error in one shot). Absent/garbage ⇒
/// the default deadline.
const ACQUIRE_DEADLINE_ENV: &str = "TRUST_MEMORY_JOBSERVER_DEADLINE_MS";

/// Initial backoff between admission retries while parked under a full budget.
/// Capped exponential backoff (never a busy-spin): each failed attempt sleeps,
/// then the delay grows up to [`MAX_ACQUIRE_BACKOFF`]. Small enough to admit
/// promptly when a peer releases, large enough to keep the flock contention and
/// CPU cost of waiting negligible.
const INITIAL_ACQUIRE_BACKOFF: Duration = Duration::from_millis(25);

/// Cap on the per-retry backoff so a long wait does not over-sleep past a
/// freed slot.
const MAX_ACQUIRE_BACKOFF: Duration = Duration::from_millis(500);

/// A token ledger is tiny in healthy operation (one short row per worker).
/// Bound the input before UTF-8 decoding/parsing so a corrupt authoritative file
/// cannot turn admission into an unbounded allocation.
const MAX_LEDGER_BYTES: u64 = 1024 * 1024;

/// Independent row-count bound for the parsed representation. At roughly one
/// row per process this is orders of magnitude beyond a real host's worker set.
const MAX_LEDGER_ROWS: usize = 32 * 1024;

/// Environment variable naming the shared token file. The orchestrator
/// (targo / the worker launcher) sets this to one exact path shared by its
/// participating workers. UNSET ⇒ no coordinator ⇒ reservations are no-ops
/// (drop-in).
const TOKEN_FILE_ENV: &str = "TRUST_MEMORY_JOBSERVER";

/// Process-wide conservative floor of the derived effective-memory budget (zero
/// means not yet observed, or genuinely unavailable). Re-measurement may lower
/// this value (for example after a Linux cgroup limit is reduced) but never raises
/// it during a process lifetime.
static BUDGET_BYTES_CACHE: AtomicU64 = AtomicU64::new(0);

/// Process-unique ingredients for unpredictable, collision-resistant temporary
/// ledger names. `create_new` remains the authoritative no-follow decision.
static TEMPORARY_SEQUENCE: AtomicU64 = AtomicU64::new(0);
static TEMPORARY_RANDOM_STATE: OnceLock<RandomState> = OnceLock::new();

/// Serializes the tests that mutate the process-global `TOKEN_FILE_ENV` /
/// `ACQUIRE_DEADLINE_ENV`. cargo runs unit tests as parallel threads in one
/// process, so without this one test's `set_var` leaks into another's
/// `is_active()` / `reserved_bytes()` read. Production sets the env once per
/// process — this is purely a test-isolation aid.
#[cfg(test)]
pub(crate) static ENV_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
thread_local! {
    /// Test-only per-thread override of the token-file path, so parallel test
    /// threads get isolated buckets without mutating the process-global
    /// `TOKEN_FILE_ENV` (which every concurrent `acquire`/`reserved_bytes` in
    /// other tests would otherwise pick up). Production never sets this;
    /// `token_file_path()` consults it only in `cfg(test)` builds.
    static TEST_TOKEN_PATH: std::cell::RefCell<Option<PathBuf>> =
        const { std::cell::RefCell::new(None) };
}

/// Test-only: set (or clear) this thread's token-file path override.
#[cfg(test)]
pub(crate) fn set_test_token_path(path: Option<PathBuf>) {
    TEST_TOKEN_PATH.with(|c| *c.borrow_mut() = path);
}

/// Fail-closed error from an explicitly configured file coordinator.
///
/// Callers must surface this as a verification failure before starting a solver;
/// it is never interchangeable with the inert, unconfigured standalone lane.
#[derive(Debug, thiserror::Error)]
pub enum MemoryJobserverError {
    /// The effective-memory budget could not be derived, so safe participating
    /// admission is impossible for a configured coordinator.
    #[error("configured memory jobserver could not derive the effective-memory budget")]
    BudgetUnavailable,
    /// One solver request can never fit within the selected authority's budget.
    #[error(
        "memory reservation request ({request_bytes} bytes) exceeds the selected coordinator budget ({budget_bytes} bytes)"
    )]
    RequestExceedsBudget { request_bytes: u64, budget_bytes: u64 },
    /// The bucket remained full through its bounded wait. Launching anyway would
    /// defeat the coordinator, so the current verification must stop.
    #[error("memory reservation was not admitted within {deadline_ms}ms")]
    AdmissionDeadline { deadline_ms: u128 },
    /// Ledger path authority, locking, parsing, arithmetic, or durable
    /// publication failed. The detailed message is suitable for diagnostics.
    #[error("memory-jobserver ledger failure: {0}")]
    Ledger(String),
}

type JobserverResult<T> = Result<T, MemoryJobserverError>;

fn ledger_error(message: impl Into<String>) -> MemoryJobserverError {
    MemoryJobserverError::Ledger(message.into())
}

#[derive(Clone, Copy)]
struct AdmissionWindow {
    end: Instant,
    timeout_ms: u128,
}

impl AdmissionWindow {
    fn new(timeout: Duration) -> Self {
        let now = Instant::now();
        // An unrepresentable duration is not a license to wait forever. Treat it
        // as an already-expired configured bound and fail closed.
        let end = now.checked_add(timeout).unwrap_or(now);
        Self { end, timeout_ms: timeout.as_millis() }
    }

    fn expired(self) -> bool {
        Instant::now() >= self.end
    }

    fn remaining(self) -> Duration {
        self.end.saturating_duration_since(Instant::now())
    }

    fn timeout_error(self) -> MemoryJobserverError {
        MemoryJobserverError::AdmissionDeadline { deadline_ms: self.timeout_ms }
    }
}

/// A held reservation in one selected memory domain. Releasing the reserved bytes
/// back to the shared token file happens automatically on `Drop`, so it is tied to
/// the lifetime of the solve that acquired it (or to a panic that unwinds through
/// it). A reservation with no backing token file (`bytes == 0` / `path == None`)
/// is an inert no-op: dropping it does nothing, which is exactly the standalone
/// `trustc` behavior.
#[derive(Debug)]
#[must_use = "the reservation is released when dropped; bind it for the solve's lifetime"]
pub struct MemoryReservation {
    /// Bytes reserved in the shared token file. `0` ⇒ inert (no coordinator).
    bytes: u64,
    /// The shared token file path, if a coordinator is active.
    path: Option<PathBuf>,
    /// PID that owns this reservation line (for prune/release matching).
    pid: u32,
}

impl MemoryReservation {
    /// An inert reservation: no coordinator, nothing reserved. Used only for
    /// the drop-in standalone path (and explicit zero-byte requests).
    #[must_use]
    pub fn inert() -> Self {
        Self { bytes: 0, path: None, pid: std::process::id() }
    }

    /// Whether this reservation actually holds bytes in a shared token file.
    #[must_use]
    pub fn is_active(&self) -> bool {
        self.bytes > 0 && self.path.is_some()
    }

    /// The number of bytes this reservation holds (0 when inert).
    #[must_use]
    pub fn bytes(&self) -> u64 {
        self.bytes
    }
}

impl Drop for MemoryReservation {
    fn drop(&mut self) {
        if self.bytes == 0 {
            return;
        }
        // A raw fork duplicates Rust memory, including this guard, but the child
        // does not own the parent's ledger row. Never let child teardown remove a
        // reservation while the parent solver remains live. Retaining the row is
        // conservative; the recording parent will release or be pruned on death.
        if std::process::id() != self.pid {
            return;
        }
        let Some(path) = self.path.clone() else {
            return;
        };
        // Best-effort release: remove THIS reservation's line and rewrite. A
        // failure here is conservative — later admission keeps counting the row
        // until this owning PID is definitely gone.
        let pid = self.pid;
        let bytes = self.bytes;
        // Release gives ordinary short writer contention a bounded wait window.
        // On expiry retain this row for PID-death pruning rather than deleting
        // without the lock or delaying an unwind indefinitely.
        let _ = rewrite_tokens_until(&path, AdmissionWindow::new(RELEASE_LOCK_DEADLINE), |lines| {
            prune_dead(lines);
            // Drop exactly one matching (pid, bytes) line — our own reservation.
            if let Some(idx) = lines.iter().position(|l| l.pid == pid && l.bytes == bytes) {
                lines.remove(idx);
            }
            Ok(())
        });
        self.bytes = 0;
    }
}

/// One reservation line in the shared token file: `pid bytes unix_ts`.
#[derive(Debug, Clone, Copy)]
struct TokenLine {
    pid: u32,
    bytes: u64,
    ts: u64,
}

impl TokenLine {
    fn parse(line: &str) -> Result<Self, String> {
        let mut it = line.split_whitespace();
        let pid = it
            .next()
            .ok_or_else(|| "missing pid".to_string())?
            .parse::<u32>()
            .map_err(|_| "pid is not a decimal u32".to_string())?;
        let bytes = it
            .next()
            .ok_or_else(|| "missing byte count".to_string())?
            .parse::<u64>()
            .map_err(|_| "byte count is not a decimal u64".to_string())?;
        let ts = it
            .next()
            .ok_or_else(|| "missing timestamp".to_string())?
            .parse::<u64>()
            .map_err(|_| "timestamp is not a decimal u64".to_string())?;
        if it.next().is_some() {
            return Err("extra token-ledger field".to_string());
        }
        if pid == 0 || pid > i32::MAX as u32 {
            return Err("pid must be in 1..=i32::MAX".to_string());
        }
        if bytes == 0 {
            return Err("byte count must be nonzero".to_string());
        }
        if ts == 0 {
            return Err("timestamp must be nonzero".to_string());
        }
        let parsed = Self { pid, bytes, ts };
        if line != parsed.render() {
            return Err("row is not in canonical 'pid bytes timestamp' form".to_string());
        }
        Ok(parsed)
    }

    fn render(&self) -> String {
        format!("{} {} {}", self.pid, self.bytes, self.ts)
    }
}

/// Parse the complete authoritative ledger. Empty means no reservations; every
/// non-empty row must be exact and valid. A malformed row is never skipped,
/// because silently dropping it would undercount live memory.
fn parse_token_ledger(contents: &str) -> Result<Vec<TokenLine>, String> {
    if contents.is_empty() {
        return Ok(Vec::new());
    }
    if contents.ends_with('\n') || contents.ends_with('\r') {
        return Err(
            "malformed token ledger row: non-canonical trailing line terminator".to_string()
        );
    }

    let mut parsed = Vec::new();
    for (index, line) in contents.lines().enumerate() {
        if index >= MAX_LEDGER_ROWS {
            return Err(format!("token ledger exceeds {MAX_LEDGER_ROWS} rows"));
        }
        if line.trim().is_empty() {
            return Err(format!("malformed token ledger row {}: empty row", index + 1));
        }
        parsed.push(
            TokenLine::parse(line)
                .map_err(|error| format!("malformed token ledger row {}: {error}", index + 1))?,
        );
    }
    Ok(parsed)
}

fn checked_reserved_bytes(lines: &[TokenLine]) -> Result<u64, String> {
    lines.iter().try_fold(0u64, |total, line| {
        total.checked_add(line.bytes).ok_or_else(|| {
            "token ledger byte aggregation overflowed u64; refusing undercount".to_string()
        })
    })
}

/// The selected ledger domain's effective-memory budget in bytes.
///
/// Derived from effective memory (host physical RAM, capped by every Linux
/// cgroup limit visible between the current group and its mounted root) scaled by
/// the default 70/100 fraction. An enclosing limit hidden above that mount is a
/// deployment/container-configuration TCB boundary. Within one process
/// the cached floor may decrease when the effective limit decreases, but never
/// increases. Returns 0 only when memory cannot be detected. An unconfigured
/// standalone caller remains inert; a configured coordinator returns
/// [`MemoryJobserverError::BudgetUnavailable`].
#[must_use]
pub fn machine_budget_bytes() -> u64 {
    let total = total_physical_memory_bytes();
    let observed = ((u128::from(total) * u128::from(DEFAULT_BUDGET_NUMERATOR))
        / u128::from(DEFAULT_BUDGET_DENOMINATOR)) as u64;
    if observed == 0 {
        return 0;
    }

    // A runtime cgroup limit can be lowered after process start. Keep a
    // monotonic conservative floor so an earlier, larger observation is never
    // allowed to override a later, smaller authority domain.
    let mut cached = BUDGET_BYTES_CACHE.load(Ordering::Acquire);
    loop {
        if cached != 0 && cached <= observed {
            return cached;
        }
        match BUDGET_BYTES_CACHE.compare_exchange_weak(
            cached,
            observed,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => return observed,
            Err(actual) => cached = actual,
        }
    }
}

/// Whether the cross-process memory-jobserver is active (a shared token file is
/// configured via `TRUST_MEMORY_JOBSERVER`). When active, even a worker that
/// never set an explicit per-job ceiling — notably the in-compiler source
/// verification path — should derive one so it participates in admission
/// control. UNSET ⇒ no coordinator ⇒ drop-in.
#[must_use]
pub fn is_active() -> bool {
    #[cfg(test)]
    if TEST_TOKEN_PATH.with(|c| c.borrow().is_some()) {
        return true;
    }
    // Presence selects the file authority. An explicitly empty value is still
    // considered configured so higher layers derive a reservation and
    // `acquire` can reject the malformed authority instead of treating it as an
    // unconfigured, inert lane.
    std::env::var_os(TOKEN_FILE_ENV).is_some()
}

/// A per-job memory ceiling (MB) derived from this process's effective budget and
/// available parallelism. It is floored at 1 GiB so one solve keeps workable
/// headroom, then capped at the whole budget; the shared coordinator, rather than
/// this estimate alone, limits the sum of concurrently accepted reservations.
/// `None` when no nonzero MiB limit can be derived. The configured acquisition
/// path rejects that state; this helper remains optional for an unconfigured
/// standalone caller.
#[must_use]
pub fn default_per_job_limit_mb() -> Option<u64> {
    let budget = machine_budget_bytes();
    let jobs = std::thread::available_parallelism().map(|n| n.get() as u64).unwrap_or(1).max(1);
    per_job_limit_mb_for(budget, jobs)
}

fn per_job_limit_mb_for(budget: u64, jobs: u64) -> Option<u64> {
    if budget == 0 {
        return None;
    }
    const MIN_PER_JOB_BYTES: u64 = 1024 * 1024 * 1024; // 1 GiB
    // `clamp(min, max)` panics when a small host has budget < 1 GiB. Express
    // the intended floor-then-cap directly so every nonzero budget is valid.
    let per_job = (budget / jobs.max(1)).max(MIN_PER_JOB_BYTES).min(budget);
    let megabytes = per_job / (1024 * 1024);
    // Returning Some(0) would make a configured caller request an inert
    // reservation. A sub-MiB effective budget is not representable by this API,
    // so fail derivation and let the configured path stop before solver launch.
    (megabytes > 0).then_some(megabytes)
}

/// Resolve the shared token file path from the environment. `Ok(None)` means no
/// coordinator is active. Presence with an empty value is a configured-but-
/// invalid authority and therefore an error, never an inert lane.
fn token_file_path() -> JobserverResult<Option<PathBuf>> {
    #[cfg(test)]
    if let Some(p) = TEST_TOKEN_PATH.with(|c| c.borrow().clone()) {
        if p.as_os_str().is_empty() {
            return Err(ledger_error(format!("{TOKEN_FILE_ENV} is configured with an empty path")));
        }
        return Ok(Some(p));
    }
    match std::env::var_os(TOKEN_FILE_ENV) {
        Some(p) if p.is_empty() => {
            Err(ledger_error(format!("{TOKEN_FILE_ENV} is configured with an empty path")))
        }
        Some(p) => Ok(Some(PathBuf::from(p))),
        None => Ok(None),
    }
}

/// Resolve the admission deadline from [`ACQUIRE_DEADLINE_ENV`], falling back to
/// [`DEFAULT_ACQUIRE_DEADLINE`]. `0` ⇒ no blocking (one grant-or-error shot).
///
// Trust: `pub(crate)` so the daemon's blocking RESERVE honors the SAME deadline
// knob (`TRUST_MEMORY_JOBSERVER_DEADLINE_MS`) as the file bucket — daemon-on and
// file-bucket admission behavior match exactly. No logic change.
pub(crate) fn acquire_deadline() -> Duration {
    match std::env::var(ACQUIRE_DEADLINE_ENV) {
        Ok(v) => match v.trim().parse::<u64>() {
            Ok(ms) => Duration::from_millis(ms),
            Err(_) => DEFAULT_ACQUIRE_DEADLINE,
        },
        Err(_) => DEFAULT_ACQUIRE_DEADLINE,
    }
}

/// A single atomic admission ATTEMPT under one exclusive flock: prune dead-owner
/// lines, and if `request_bytes` fits under `budget`, claim them. Returns
/// `Ok(true)` if granted, `Ok(false)` if the budget is momentarily full, and
/// `Err` on any authority, format, arithmetic, or I/O failure.
///
/// The flock is held ONLY for the duration of this one read-check-write — it is
/// released before the caller sleeps between retries, so a worker waiting for
/// admission never holds the lock while parked. This is what makes blocking
/// deadlock-free: the lock a releasing peer needs to free its bytes is never
/// pinned by a waiter.
fn try_admit(
    path: &Path,
    pid: u32,
    request_bytes: u64,
    budget: u64,
    window: AdmissionWindow,
) -> JobserverResult<bool> {
    let path = authoritative_token_path(path)?;
    try_admit_authoritative(&path, pid, request_bytes, budget, window)
}

/// Admission against a path that was already resolved and authority-checked.
/// `acquire` deliberately calls this variant for every retry so cwd/symlink
/// changes cannot redirect later attempts into a second bucket.
fn try_admit_authoritative(
    path: &Path,
    pid: u32,
    request_bytes: u64,
    budget: u64,
    window: AdmissionWindow,
) -> JobserverResult<bool> {
    let now = unix_now();
    if now == 0 {
        return Err(ledger_error("system clock is before the Unix epoch"));
    }
    let mut granted = false;
    rewrite_authoritative_tokens_with_hook_until(
        path,
        window,
        |lines| {
            // A budget may have been lowered since an older row was granted.
            // Reclaim definitely-dead owners first; only a SURVIVING oversized
            // row blocks admission. The full ledger was already parsed and its
            // aggregate checked before this edit, so pruning cannot launder a
            // malformed/overflowed input.
            prune_dead(lines);
            if let Some(line) = lines.iter().find(|line| line.bytes > budget) {
                return Err(ledger_error(format!(
                    "reservation row for pid {} exceeds the selected coordinator budget",
                    line.pid
                )));
            }
            let reserved = checked_reserved_bytes(lines).map_err(ledger_error)?;
            let with_request = reserved.checked_add(request_bytes).ok_or_else(|| {
                ledger_error("reservation plus request overflowed u64; refusing undercount")
            })?;
            if with_request <= budget {
                lines.push(TokenLine { pid, bytes: request_bytes, ts: now });
                granted = true;
            }
            Ok(())
        },
        |_| Ok(()),
    )?;
    Ok(granted)
}

/// Acquire a reservation of `request_bytes` against the selected ledger's shared
/// budget before beginning same-owner solver work. This is the cross-process
/// chokepoint that stops participating workers using this exact path from
/// collectively reserving beyond its allowance. The reservation stays with its
/// recording PID; external child ownership transfer is unsupported. Other
/// ledgers, unconfigured processes, and actual RSS outside the per-process guard
/// are not machine-wide enforcement by this file.
///
/// Behavior:
/// * No coordinator (no token file env) ⇒ returns an inert reservation that
///   always succeeds. Standalone `trustc` is unchanged (DROP-IN).
/// * Coordinator present and the request fits under the budget once dead-owner lines
///   are pruned ⇒ returns an ACTIVE reservation holding `request_bytes`.
/// * Coordinator present but the budget is momentarily FULL ⇒ this is admission
///   CONTROL: the call BLOCKS, sleeping with capped exponential backoff and
///   re-checking, until either the request fits (peers released bytes) or the
///   [`acquire_deadline`] contention window elapses. Expiry returns an error;
///   callers must stop before spawning. We NEVER busy-spin and NEVER hold the
///   flock while parked. Synchronous filesystem I/O is covered by the authority
///   contract above, not preempted by this wait window.
///
/// `request_bytes == 0` is inert after the configured path's static authority is
/// validated. It does not open or parse the ledger because it holds no shared
/// resource; malformed path selection still fails closed.
#[must_use]
pub fn acquire(request_bytes: u64) -> Result<MemoryReservation, MemoryJobserverError> {
    let configured_path = token_file_path()?;
    if request_bytes == 0 {
        // Zero reserves no bytes, but an explicitly configured path is still
        // selected: validate its static authority rather than letting an empty,
        // relative, or aliased path masquerade as the unconfigured lane.
        if let Some(raw_path) = configured_path.as_deref() {
            authoritative_token_path(raw_path)?;
        }
        return Ok(MemoryReservation::inert());
    }
    let Some(raw_path) = configured_path else {
        return Ok(MemoryReservation::inert());
    };
    // Resolve the authority exactly once before the retry loop. In particular,
    // never retain a relative/aliased spelling whose meaning can change after a
    // process-wide cwd change or symlink retarget; Drop receives this frozen
    // absolute path too.
    let path = authoritative_token_path(&raw_path)?;
    let budget = machine_budget_bytes();
    if budget == 0 {
        return Err(MemoryJobserverError::BudgetUnavailable);
    }
    // A request that can NEVER fit (larger than the whole budget) must not block
    // for the full deadline — no peer release can ever satisfy it. Fail before
    // spawn instead of bypassing the configured aggregate authority.
    if request_bytes > budget {
        return Err(MemoryJobserverError::RequestExceedsBudget {
            request_bytes,
            budget_bytes: budget,
        });
    }
    let pid = std::process::id();
    let window = AdmissionWindow::new(acquire_deadline());
    let mut backoff = INITIAL_ACQUIRE_BACKOFF;

    loop {
        match try_admit_authoritative(&path, pid, request_bytes, budget, window) {
            // Granted: hand back an ACTIVE reservation; RAII Drop releases it on
            // EVERY exit path (success, error, panic-unwind) of the holder.
            Ok(true) => {
                return Ok(MemoryReservation { bytes: request_bytes, path: Some(path), pid });
            }
            // Budget momentarily full. Block (sleep + retry) until a peer frees
            // bytes or the deadline elapses, then fail closed.
            Ok(false) => {
                if window.expired() {
                    return Err(window.timeout_error());
                }
                // Sleep before retrying — NEVER a busy-spin. Cap the nap at the
                // remaining time so we do not over-sleep past the deadline.
                std::thread::sleep(backoff.min(window.remaining()));
                backoff = (backoff * 2).min(MAX_ACQUIRE_BACKOFF);
            }
            Err(error) => return Err(error),
        }
    }
}

/// Total reserved bytes currently recorded in the shared token file (after
/// pruning dead-owner lines). Returns `Ok(0)` when no coordinator is active. A
/// configured, unreadable or invalid ledger is an error, never a false zero.
/// Diagnostic / test helper — the hot path uses [`acquire`] atomically.
#[must_use]
pub fn reserved_bytes() -> Result<u64, MemoryJobserverError> {
    let Some(path) = token_file_path()? else {
        return Ok(0);
    };
    let mut total = 0u64;
    rewrite_tokens(&path, |lines| {
        prune_dead(lines);
        total = checked_reserved_bytes(lines).map_err(ledger_error)?;
        Ok(())
    })?;
    Ok(total)
}

/// Remove only reservation lines whose owning PID is definitely no longer alive.
/// A timestamp is diagnostic/backward-compatible data, never authority to erase
/// a live worker: doing so would undercount a valid long-running solve.
fn prune_dead(lines: &mut Vec<TokenLine>) {
    lines.retain(|line| pid_is_alive(line.pid));
}

/// Read the token file under one stable exclusive flock, apply `edit`, and
/// durably publish the exact result. The configured path is an authority: its
/// parent/ancestor chain, lock sentinel, and ledger leaf are validated before
/// their contents can affect admission. Same-euid processes are the cooperating
/// principals of one build; cross-user replacement is excluded by the validated
/// non-writable directory chain, while deterministic same-euid replacements are
/// detected at every operation boundary by inode checks.
fn rewrite_tokens<F>(path: &Path, edit: F) -> JobserverResult<()>
where
    F: FnOnce(&mut Vec<TokenLine>) -> JobserverResult<()>,
{
    rewrite_tokens_until(path, AdmissionWindow::new(acquire_deadline()), edit)
}

fn rewrite_tokens_until<F>(path: &Path, window: AdmissionWindow, edit: F) -> JobserverResult<()>
where
    F: FnOnce(&mut Vec<TokenLine>) -> JobserverResult<()>,
{
    rewrite_tokens_with_hook_until(path, window, edit, |_| Ok(()))
}

/// Test seam for a deterministic lock-path replacement after acquisition. The
/// production wrapper above always supplies a no-op hook.
fn rewrite_tokens_with_hook<F, H>(path: &Path, edit: F, after_lock: H) -> JobserverResult<()>
where
    F: FnOnce(&mut Vec<TokenLine>) -> JobserverResult<()>,
    H: FnOnce(&Path) -> JobserverResult<()>,
{
    rewrite_tokens_with_hook_until(path, AdmissionWindow::new(acquire_deadline()), edit, after_lock)
}

fn rewrite_tokens_with_hook_until<F, H>(
    path: &Path,
    window: AdmissionWindow,
    edit: F,
    after_lock: H,
) -> JobserverResult<()>
where
    F: FnOnce(&mut Vec<TokenLine>) -> JobserverResult<()>,
    H: FnOnce(&Path) -> JobserverResult<()>,
{
    let path = authoritative_token_path(path)?;
    rewrite_authoritative_tokens_with_hook_until(&path, window, edit, after_lock)
}

fn rewrite_authoritative_tokens_with_hook_until<F, H>(
    path: &Path,
    window: AdmissionWindow,
    edit: F,
    after_lock: H,
) -> JobserverResult<()>
where
    F: FnOnce(&mut Vec<TokenLine>) -> JobserverResult<()>,
    H: FnOnce(&Path) -> JobserverResult<()>,
{
    let lock = AuthoritativeLock::acquire(&path, window)?;
    after_lock(lock.path())?;
    lock.validate_path()?;

    let (mut lines, expected_ledger) = read_token_file(&path)?;
    // Validate the authoritative input before allowing any edit (including
    // stale pruning or release) to erase evidence of a wrapped aggregate.
    checked_reserved_bytes(&lines).map_err(ledger_error)?;
    edit(&mut lines)?;
    // Re-check arithmetic after the edit too: neither future call sites nor a
    // malformed mutation may publish a ledger whose total silently wraps.
    checked_reserved_bytes(&lines).map_err(ledger_error)?;

    let body = lines.iter().map(TokenLine::render).collect::<Vec<_>>().join("\n");
    lock.validate_path()?;
    publish_token_file(&path, body.as_bytes(), expected_ledger)?;
    lock.validate_path()?;
    Ok(())
}

/// Resolve one absolute, unaliased parent and use only that canonical result
/// thereafter. Rejecting relative paths and any spelling whose parent differs
/// from its canonical path prevents cwd changes or a mutable symlink alias from
/// splitting one configured authority into several independently-full ledgers.
/// The leaf itself must remain a single ordinary filename; it is never
/// canonicalized through an attacker-controlled symlink.
fn authoritative_token_path(path: &Path) -> JobserverResult<PathBuf> {
    #[cfg(not(unix))]
    {
        let _ = path;
        return Err(ledger_error(
            "the file memory coordinator is unsupported on this platform because owner/mode, no-follow, and stable-inode authority cannot be established",
        ));
    }

    #[cfg(unix)]
    {
        if !path.is_absolute() {
            return Err(ledger_error(format!(
                "token path must be absolute so its authority cannot change with cwd: {}",
                path.display()
            )));
        }
        let file_name = path.file_name().ok_or_else(|| {
            ledger_error(format!("token path has no filename: {}", path.display()))
        })?;
        let parent = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent,
            _ => Path::new("."),
        };
        let canonical_parent = std::fs::canonicalize(parent).map_err(|error| {
            ledger_error(format!(
                "token parent cannot be resolved (it must already exist): {}: {error}",
                parent.display()
            ))
        })?;
        if canonical_parent.as_os_str() != parent.as_os_str() {
            return Err(ledger_error(format!(
                "token parent must already be canonical (no '.', '..', or symlink aliases): configured {}, canonical {}",
                parent.display(),
                canonical_parent.display()
            )));
        }
        validate_authoritative_directory_chain(&canonical_parent)?;
        let authoritative = canonical_parent.join(file_name);
        if authoritative.as_os_str() != path.as_os_str() {
            return Err(ledger_error(format!(
                "token path must use one exact canonical spelling: configured {}, authoritative {}",
                path.display(),
                authoritative.display()
            )));
        }
        Ok(authoritative)
    }
}

fn validate_authoritative_directory_chain(parent: &Path) -> JobserverResult<()> {
    #[cfg(unix)]
    let euid = unsafe {
        // SAFETY: `geteuid` has no arguments or memory effects and always returns
        // the effective uid of this process.
        libc::geteuid()
    };

    for (index, directory) in parent.ancestors().enumerate() {
        let metadata = std::fs::symlink_metadata(directory).map_err(|error| {
            ledger_error(format!("cannot inspect token ancestor {}: {error}", directory.display()))
        })?;
        if !metadata.file_type().is_dir() {
            return Err(ledger_error(format!(
                "token ancestor is not a directory: {}",
                directory.display()
            )));
        }

        #[cfg(unix)]
        {
            let mode = metadata.mode() & 0o777;
            if metadata.uid() != 0 && metadata.uid() != euid {
                return Err(ledger_error(format!(
                    "token ancestor is foreign-owned: {}",
                    directory.display()
                )));
            }
            if mode & 0o022 != 0 {
                return Err(ledger_error(format!(
                    "token ancestor is group/other writable: {}",
                    directory.display()
                )));
            }
            if index == 0 && metadata.uid() != euid {
                return Err(ledger_error(format!(
                    "token parent must be owned by effective uid {euid}: {}",
                    directory.display()
                )));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(not(unix))]
    length: u64,
    #[cfg(not(unix))]
    modified: Option<SystemTime>,
}

impl FileIdentity {
    fn from_metadata(metadata: &std::fs::Metadata) -> Self {
        Self {
            #[cfg(unix)]
            device: metadata.dev(),
            #[cfg(unix)]
            inode: metadata.ino(),
            #[cfg(not(unix))]
            length: metadata.len(),
            #[cfg(not(unix))]
            modified: metadata.modified().ok(),
        }
    }
}

fn validate_private_regular_file(
    metadata: &std::fs::Metadata,
    path: &Path,
    description: &str,
) -> JobserverResult<FileIdentity> {
    if !metadata.file_type().is_file() {
        return Err(ledger_error(format!(
            "{description} is not a regular file: {}",
            path.display()
        )));
    }

    #[cfg(unix)]
    {
        let euid = unsafe {
            // SAFETY: `geteuid` has no arguments or memory effects.
            libc::geteuid()
        };
        if metadata.uid() != euid {
            return Err(ledger_error(format!(
                "{description} is not owned by effective uid {euid}: {}",
                path.display()
            )));
        }
        if metadata.mode() & 0o077 != 0 {
            return Err(ledger_error(format!(
                "{description} grants group/other permissions: {}",
                path.display()
            )));
        }
        if metadata.nlink() != 1 {
            return Err(ledger_error(format!(
                "{description} must have exactly one link: {}",
                path.display()
            )));
        }
    }

    Ok(FileIdentity::from_metadata(metadata))
}

fn validate_path_identity(
    path: &Path,
    expected: FileIdentity,
    description: &str,
) -> JobserverResult<()> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        ledger_error(format!("cannot inspect {description} {}: {error}", path.display()))
    })?;
    let actual = validate_private_regular_file(&metadata, path, description)?;
    if actual != expected {
        return Err(ledger_error(format!(
            "{description} was replaced during the locked operation: {}",
            path.display()
        )));
    }
    Ok(())
}

fn lock_path_for(path: &Path) -> PathBuf {
    let mut lock_path = path.as_os_str().to_owned();
    lock_path.push(".lock");
    PathBuf::from(lock_path)
}

#[cfg(target_os = "linux")]
const MAX_LOCK_DOMAIN_BYTES: u64 = 128;

#[cfg(target_os = "linux")]
fn linux_pid_namespace_marker() -> JobserverResult<String> {
    let metadata = std::fs::metadata("/proc/self/ns/pid").map_err(|error| {
        ledger_error(format!("cannot inspect current Linux PID namespace: {error}"))
    })?;
    Ok(format!("trust-memory-jobserver-lock-v1 pidns={}:{}\n", metadata.dev(), metadata.ino()))
}

#[cfg(unix)]
struct AuthoritativeLock {
    file: File,
    path: PathBuf,
    identity: FileIdentity,
}

#[cfg(unix)]
impl AuthoritativeLock {
    fn acquire(token_path: &Path, window: AdmissionWindow) -> JobserverResult<Self> {
        let path = lock_path_for(token_path);
        let mut options = OpenOptions::new();
        options
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            // NONBLOCK prevents a pre-existing FIFO/device leaf from wedging
            // before the post-open regular-file validation can reject it.
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK);
        let file = options.open(&path).map_err(|error| {
            ledger_error(format!("cannot open private lock sentinel {}: {error}", path.display()))
        })?;
        let identity = validate_private_regular_file(
            &file.metadata().map_err(|error| {
                ledger_error(format!(
                    "cannot inspect open lock sentinel {}: {error}",
                    path.display()
                ))
            })?,
            &path,
            "memory-jobserver lock sentinel",
        )?;
        validate_path_identity(&path, identity, "memory-jobserver lock sentinel")?;

        let mut backoff = INITIAL_ACQUIRE_BACKOFF;
        loop {
            // SAFETY: `file` owns a live descriptor and `LOCK_EX | LOCK_NB`
            // only changes its advisory lock state. The descriptor remains open
            // in the returned guard. Nonblocking mode keeps the configured
            // admission deadline authoritative even when another holder wedges.
            if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
                break;
            }
            let error = std::io::Error::last_os_error();
            if error.kind() != std::io::ErrorKind::WouldBlock {
                return Err(ledger_error(format!(
                    "cannot acquire lock sentinel {}: {error}",
                    path.display()
                )));
            }
            if window.expired() {
                return Err(window.timeout_error());
            }
            std::thread::sleep(backoff.min(window.remaining()));
            backoff = (backoff * 2).min(MAX_ACQUIRE_BACKOFF);
        }
        let mut lock = Self { file, path, identity };
        lock.validate_process_domain(token_path)?;
        lock.validate_path()?;
        Ok(lock)
    }

    fn path(&self) -> &Path {
        &self.path
    }

    #[cfg(target_os = "linux")]
    fn validate_process_domain(&mut self, token_path: &Path) -> JobserverResult<()> {
        let expected = linux_pid_namespace_marker()?;
        let length = self
            .file
            .metadata()
            .map_err(|error| {
                ledger_error(format!(
                    "cannot inspect lock-domain marker {}: {error}",
                    self.path.display()
                ))
            })?
            .len();
        if length == 0 {
            // Empty is the legacy/new sentinel state. It may be stamped only
            // while no live rows exist: otherwise a restored lock or a process
            // in another PID namespace could adopt the ledger and mis-prune
            // foreign-but-live PIDs. Parsing/authority errors also fail closed.
            let (existing, _) = read_token_file(token_path)?;
            if !existing.is_empty() {
                return Err(ledger_error(format!(
                    "empty lock-domain marker refuses to adopt non-empty ledger {}; quiesce all workers and remove the private ledger and lock together before retrying",
                    token_path.display()
                )));
            }
            self.file.seek(SeekFrom::Start(0)).map_err(|error| {
                ledger_error(format!(
                    "cannot position new lock-domain marker {}: {error}",
                    self.path.display()
                ))
            })?;
            self.file.write_all(expected.as_bytes()).and_then(|()| self.file.sync_all()).map_err(
                |error| {
                    ledger_error(format!(
                        "cannot initialize lock-domain marker {}: {error}",
                        self.path.display()
                    ))
                },
            )?;
            return Ok(());
        }
        if length > MAX_LOCK_DOMAIN_BYTES {
            return Err(ledger_error(format!(
                "lock-domain marker exceeds {MAX_LOCK_DOMAIN_BYTES} bytes: {}",
                self.path.display()
            )));
        }
        self.file.seek(SeekFrom::Start(0)).map_err(|error| {
            ledger_error(format!(
                "cannot position lock-domain marker {}: {error}",
                self.path.display()
            ))
        })?;
        let mut bytes = Vec::new();
        Read::by_ref(&mut self.file)
            .take(MAX_LOCK_DOMAIN_BYTES + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| {
                ledger_error(format!(
                    "cannot read lock-domain marker {}: {error}",
                    self.path.display()
                ))
            })?;
        if bytes != expected.as_bytes() {
            return Err(ledger_error(format!(
                "lock-domain marker does not match this Linux PID namespace: {}",
                self.path.display()
            )));
        }
        Ok(())
    }

    #[cfg(not(target_os = "linux"))]
    fn validate_process_domain(&mut self, _token_path: &Path) -> JobserverResult<()> {
        Ok(())
    }

    fn validate_path(&self) -> JobserverResult<()> {
        let open_identity = validate_private_regular_file(
            &self.file.metadata().map_err(|error| {
                ledger_error(format!(
                    "cannot reinspect open lock sentinel {}: {error}",
                    self.path.display()
                ))
            })?,
            &self.path,
            "memory-jobserver lock sentinel",
        )?;
        if open_identity != self.identity {
            return Err(ledger_error(format!(
                "open lock sentinel identity changed: {}",
                self.path.display()
            )));
        }
        validate_path_identity(&self.path, self.identity, "memory-jobserver lock sentinel")
    }
}

#[cfg(unix)]
impl Drop for AuthoritativeLock {
    fn drop(&mut self) {
        // SAFETY: this is the same live descriptor locked in `acquire`. Closing
        // would also release it; explicit unlock makes the lifetime obvious.
        let _ = unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
    }
}

#[cfg(not(unix))]
struct AuthoritativeLock {
    _guard: coordination::CacheLockGuard,
    path: PathBuf,
}

#[cfg(not(unix))]
impl AuthoritativeLock {
    fn acquire(token_path: &Path, window: AdmissionWindow) -> JobserverResult<Self> {
        let config = CoordinationConfig::default();
        let mut backoff = INITIAL_ACQUIRE_BACKOFF;
        let guard = loop {
            match coordination::try_exclusive_lock(token_path, &config)
                .map_err(|error| ledger_error(format!("cannot acquire token lock: {error}")))?
            {
                Some(guard) => break guard,
                None if window.expired() => return Err(window.timeout_error()),
                None => {
                    std::thread::sleep(backoff.min(window.remaining()));
                    backoff = (backoff * 2).min(MAX_ACQUIRE_BACKOFF);
                }
            }
        };
        let path = guard.lock_path().to_path_buf();
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| {
            ledger_error(format!("cannot inspect lock sentinel {}: {error}", path.display()))
        })?;
        validate_private_regular_file(&metadata, &path, "memory-jobserver lock sentinel")?;
        Ok(Self { _guard: guard, path })
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn validate_path(&self) -> JobserverResult<()> {
        let metadata = std::fs::symlink_metadata(&self.path).map_err(|error| {
            ledger_error(format!("cannot reinspect lock sentinel {}: {error}", self.path.display()))
        })?;
        validate_private_regular_file(&metadata, &self.path, "memory-jobserver lock sentinel")?;
        Ok(())
    }
}

fn read_token_file(path: &Path) -> JobserverResult<(Vec<TokenLine>, Option<FileIdentity>)> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    // A configured non-regular leaf must be rejected after open without letting
    // FIFO/device open semantics exceed the cooperative wait deadline first.
    options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK);

    let mut file = match options.open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok((Vec::new(), None));
        }
        Err(error) => {
            return Err(ledger_error(format!(
                "cannot open token ledger {}: {error}",
                path.display()
            )));
        }
    };
    let metadata = file.metadata().map_err(|error| {
        ledger_error(format!("cannot inspect open token ledger {}: {error}", path.display()))
    })?;
    let identity = validate_private_regular_file(&metadata, path, "memory-jobserver token ledger")?;
    validate_path_identity(path, identity, "memory-jobserver token ledger")?;
    if metadata.len() > MAX_LEDGER_BYTES {
        return Err(ledger_error(format!(
            "token ledger exceeds {MAX_LEDGER_BYTES} bytes: {}",
            path.display()
        )));
    }

    let lines = read_and_parse_token_ledger(Read::by_ref(&mut file), path)?;
    validate_path_identity(path, identity, "memory-jobserver token ledger")?;
    Ok((lines, Some(identity)))
}

fn read_and_parse_token_ledger<R: Read>(reader: R, path: &Path) -> JobserverResult<Vec<TokenLine>> {
    let mut bytes = Vec::new();
    reader.take(MAX_LEDGER_BYTES + 1).read_to_end(&mut bytes).map_err(|error| {
        ledger_error(format!("cannot read token ledger {}: {error}", path.display()))
    })?;
    if bytes.len() as u64 > MAX_LEDGER_BYTES {
        return Err(ledger_error(format!(
            "token ledger grew beyond {MAX_LEDGER_BYTES} bytes while reading: {}",
            path.display()
        )));
    }
    let contents = String::from_utf8(bytes).map_err(|error| {
        ledger_error(format!("token ledger is not UTF-8 ({}): {error}", path.display()))
    })?;
    parse_token_ledger(&contents).map_err(ledger_error)
}

struct TemporaryLedger {
    path: PathBuf,
    file: File,
}

impl Drop for TemporaryLedger {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn secure_temporary_ledger(target: &Path, bytes: &[u8]) -> JobserverResult<TemporaryLedger> {
    for _ in 0..128 {
        let path = unique_temporary_path(target);
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600).custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK);

        let mut file = match options.open(&path) {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => {
                return Err(ledger_error(format!(
                    "cannot create private temporary ledger {}: {error}",
                    path.display()
                )));
            }
        };
        if let Err(error) = file.write_all(bytes).and_then(|()| file.sync_all()) {
            let _ = std::fs::remove_file(&path);
            return Err(ledger_error(format!(
                "cannot durably write temporary ledger {}: {error}",
                path.display()
            )));
        }
        let temporary = TemporaryLedger { path, file };
        validate_private_regular_file(
            &temporary.file.metadata().map_err(|error| {
                ledger_error(format!(
                    "cannot inspect temporary ledger {}: {error}",
                    temporary.path.display()
                ))
            })?,
            &temporary.path,
            "memory-jobserver temporary ledger",
        )?;
        return Ok(temporary);
    }
    Err(ledger_error("could not allocate a unique private temporary ledger after 128 attempts"))
}

fn unique_temporary_path(target: &Path) -> PathBuf {
    let sequence = TEMPORARY_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let random_state = TEMPORARY_RANDOM_STATE.get_or_init(RandomState::new);
    let mut hasher = random_state.build_hasher();
    target.hash(&mut hasher);
    std::process::id().hash(&mut hasher);
    sequence.hash(&mut hasher);
    let nonce = hasher.finish();
    target.parent().unwrap_or_else(|| Path::new(".")).join(format!(
        ".trust-memory-jobserver-{:x}-{sequence:016x}-{nonce:016x}.tmp",
        std::process::id()
    ))
}

fn publish_token_file(
    path: &Path,
    bytes: &[u8],
    expected: Option<FileIdentity>,
) -> JobserverResult<()> {
    let temporary = secure_temporary_ledger(path, bytes)?;
    let temporary_identity = validate_private_regular_file(
        &temporary.file.metadata().map_err(|error| {
            ledger_error(format!(
                "cannot reinspect temporary ledger {}: {error}",
                temporary.path.display()
            ))
        })?,
        &temporary.path,
        "memory-jobserver temporary ledger",
    )?;

    match expected {
        Some(expected) => {
            validate_path_identity(path, expected, "memory-jobserver token ledger")?;
            // The validated private ancestor chain excludes cross-user mutation.
            // Same-euid participants are the coordinating build's trusted
            // writers; the post-rename inode check detects accidental replacement.
            std::fs::rename(&temporary.path, path).map_err(|error| {
                ledger_error(format!("cannot replace token ledger {}: {error}", path.display()))
            })?;
        }
        None => {
            match std::fs::symlink_metadata(path) {
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Ok(_) => {
                    return Err(ledger_error(format!(
                        "token ledger appeared before no-clobber publication: {}",
                        path.display()
                    )));
                }
                Err(error) => {
                    return Err(ledger_error(format!(
                        "cannot inspect absent token ledger {}: {error}",
                        path.display()
                    )));
                }
            }
            // Hard-link publication is the atomic create-if-absent decision. It
            // cannot overwrite a regular file or a dangling symlink.
            std::fs::hard_link(&temporary.path, path).map_err(|error| {
                ledger_error(format!(
                    "cannot publish new token ledger without clobbering {}: {error}",
                    path.display()
                ))
            })?;
            std::fs::remove_file(&temporary.path).map_err(|error| {
                ledger_error(format!(
                    "cannot remove published ledger's temporary link {}: {error}",
                    temporary.path.display()
                ))
            })?;
        }
    }

    validate_path_identity(path, temporary_identity, "published memory-jobserver token ledger")?;
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    File::open(parent).and_then(|directory| directory.sync_all()).map_err(|error| {
        ledger_error(format!("cannot sync token-ledger directory {}: {error}", parent.display()))
    })?;
    Ok(())
}

fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// Is `pid` a live process? Uses `kill(pid, 0)`, which performs the permission/
/// existence check WITHOUT sending a signal — the standard no-subprocess
/// liveness probe. A pid we cannot probe is conservatively treated as alive so
/// we never reclaim a reservation we are unsure about.
// The file bucket uses this only after its stable lock has bound all Linux
// participants to one PID namespace. trustd owns separate peer-lifecycle
// accounting and does not use this file-ledger pruning helper.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn pid_is_alive(pid: u32) -> bool {
    // A live process is a single positive pid in `1..=i32::MAX`. `0` (a process
    // group) and any value that casts to a negative `pid_t` (>= 2^31, e.g. a
    // corrupt token line) make `kill(0/-1, 0)` spuriously succeed ("group / all
    // processes"), so treat both as dead and reclaim their bytes.
    if pid == 0 || pid > i32::MAX as u32 {
        return false;
    }
    // SAFETY: `kill` with signal 0 sends no signal; it only validates that the
    // target pid exists and is signalable. No memory is read or written.
    let ret = unsafe { libc::kill(pid as libc::pid_t, 0) };
    if ret == 0 {
        return true;
    }
    // ESRCH ⇒ no such process (reclaim). EPERM ⇒ alive but not ours (keep).
    std::io::Error::last_os_error().raw_os_error() != Some(libc::ESRCH)
}

// Keep the same private file-ledger helper shape on other targets.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn pid_is_alive(_pid: u32) -> bool {
    // No portable probe — retain the reservation rather than undercount it.
    true
}

/// Effective memory available to this process in bytes: physical RAM on macOS,
/// and physical RAM capped by every cgroup limit visible from the current group
/// through its mounted root on Linux. An enclosing cap hidden above the mount is
/// a deployment/container-configuration TCB boundary. Returns 0 when the visible
/// authority cannot be inspected safely. Mirrors the small part of
/// `ay_sys::physical_memory_bytes` we need without pulling the ay-sys dependency
/// (whose transitive deps conflict with compiler-pinned workspace crates).
#[cfg(target_os = "macos")]
fn total_physical_memory_bytes() -> u64 {
    let mut size: u64 = 0;
    let mut len = std::mem::size_of::<u64>();
    let name = c"hw.memsize";
    // SAFETY: `name` is a valid null-terminated C string; `size`/`len` are owned
    // stack locals with exclusive mutable access and layouts matching the
    // `u64`/`size_t` `sysctlbyname` writes. The new-value pointer is null with
    // newlen 0, the documented read-only usage.
    let ret = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            std::ptr::addr_of_mut!(size).cast::<libc::c_void>(),
            &raw mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if ret == 0 { size } else { 0 }
}

#[cfg(target_os = "linux")]
const MAX_CGROUP_METADATA_BYTES: u64 = 1024 * 1024;
#[cfg(target_os = "linux")]
const MAX_CGROUP_ANCESTORS: usize = 1024;

#[cfg(target_os = "linux")]
#[derive(Debug, Default, PartialEq, Eq)]
struct LinuxCgroupMemberships {
    unified: Option<PathBuf>,
    v1_memory: Option<PathBuf>,
}

#[cfg(target_os = "linux")]
fn clean_absolute_cgroup_path(value: &str) -> Option<PathBuf> {
    use std::path::Component;

    let path = PathBuf::from(value);
    if !path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::RootDir | Component::Normal(_)))
    {
        return None;
    }
    Some(path)
}

#[cfg(target_os = "linux")]
fn parse_linux_cgroup_memberships(contents: &str) -> Result<LinuxCgroupMemberships, String> {
    let mut memberships = LinuxCgroupMemberships::default();
    for (index, line) in contents.lines().enumerate() {
        if line.is_empty() {
            continue;
        }
        let mut fields = line.splitn(3, ':');
        let hierarchy = fields.next().unwrap_or_default();
        let controllers = fields.next().ok_or_else(|| {
            format!("malformed /proc/self/cgroup row {}: missing controllers", index + 1)
        })?;
        let raw_path = fields.next().ok_or_else(|| {
            format!("malformed /proc/self/cgroup row {}: missing path", index + 1)
        })?;
        let path = clean_absolute_cgroup_path(raw_path)
            .ok_or_else(|| format!("malformed /proc/self/cgroup row {}: unsafe path", index + 1))?;

        if hierarchy == "0" && controllers.is_empty() {
            if memberships.unified.replace(path).is_some() {
                return Err("multiple unified cgroup memberships".to_string());
            }
        } else if controllers.split(',').any(|controller| controller == "memory")
            && memberships.v1_memory.replace(path).is_some()
        {
            return Err("multiple cgroup-v1 memory memberships".to_string());
        }
    }
    Ok(memberships)
}

#[cfg(target_os = "linux")]
fn decode_mountinfo_path(value: &str) -> Result<PathBuf, String> {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let input = value.as_bytes();
    let mut decoded = Vec::with_capacity(input.len());
    let mut index = 0;
    while index < input.len() {
        if input[index] != b'\\' {
            decoded.push(input[index]);
            index += 1;
            continue;
        }
        if index + 3 >= input.len()
            || !input[index + 1..=index + 3].iter().all(u8::is_ascii_digit)
            || input[index + 1..=index + 3].iter().any(|digit| *digit > b'7')
        {
            return Err("malformed mountinfo path escape".to_string());
        }
        let byte = u16::from(input[index + 1] - b'0') * 64
            + u16::from(input[index + 2] - b'0') * 8
            + u16::from(input[index + 3] - b'0');
        decoded.push(
            u8::try_from(byte).map_err(|_| "mountinfo path escape exceeds one byte".to_string())?,
        );
        index += 4;
    }
    let path = PathBuf::from(OsString::from_vec(decoded));
    if !path.is_absolute()
        || path.components().any(|component| {
            !matches!(component, std::path::Component::RootDir | std::path::Component::Normal(_))
        })
    {
        return Err("mountinfo cgroup path is not absolute".to_string());
    }
    Ok(path)
}

#[cfg(target_os = "linux")]
fn linux_cgroup_directory(
    mountinfo: &str,
    membership: &Path,
    unified: bool,
) -> Result<Option<(PathBuf, PathBuf)>, String> {
    let mut best: Option<(usize, PathBuf, PathBuf)> = None;
    for (index, line) in mountinfo.lines().enumerate() {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        let Some(separator) = fields.iter().position(|field| *field == "-") else {
            return Err(format!("malformed /proc/self/mountinfo row {}", index + 1));
        };
        if separator < 6 || fields.len() <= separator + 3 {
            return Err(format!("malformed /proc/self/mountinfo row {}", index + 1));
        }
        let filesystem = fields[separator + 1];
        let correct_filesystem = if unified {
            filesystem == "cgroup2"
        } else {
            filesystem == "cgroup"
                && fields[separator + 3..]
                    .iter()
                    .flat_map(|field| field.split(','))
                    .any(|option| option == "memory")
        };
        if !correct_filesystem {
            continue;
        }

        let root = decode_mountinfo_path(fields[3])?;
        let mount_point = decode_mountinfo_path(fields[4])?;
        let Ok(relative) = membership.strip_prefix(&root) else {
            continue;
        };
        let specificity = root.components().count();
        let candidate = mount_point.join(relative);
        if best.as_ref().is_none_or(|(current, _, _)| specificity > *current) {
            best = Some((specificity, candidate, mount_point));
        }
    }
    Ok(best.map(|(_, path, mount_point)| (path, mount_point)))
}

#[cfg(target_os = "linux")]
fn read_bounded_linux_control(path: &Path) -> Result<String, String> {
    read_bounded_linux_control_optional(path)?
        .ok_or_else(|| format!("Linux memory authority is missing: {}", path.display()))
}

#[cfg(target_os = "linux")]
fn read_bounded_linux_control_optional(path: &Path) -> Result<Option<String>, String> {
    let file = match File::open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(format!("cannot open Linux memory authority {}: {error}", path.display()));
        }
    };
    let mut bytes = Vec::new();
    file.take(MAX_CGROUP_METADATA_BYTES + 1).read_to_end(&mut bytes).map_err(|error| {
        format!("cannot read Linux memory authority {}: {error}", path.display())
    })?;
    if bytes.len() as u64 > MAX_CGROUP_METADATA_BYTES {
        return Err(format!(
            "Linux memory authority exceeds {MAX_CGROUP_METADATA_BYTES} bytes: {}",
            path.display()
        ));
    }
    String::from_utf8(bytes).map(Some).map_err(|error| {
        format!("Linux memory authority is not UTF-8 ({}): {error}", path.display())
    })
}

#[cfg(target_os = "linux")]
fn parse_linux_memory_limit(contents: &str) -> Result<Option<u64>, String> {
    let value = contents.trim();
    if value == "max" {
        return Ok(None);
    }
    if value.is_empty() || value.split_whitespace().count() != 1 {
        return Err("malformed Linux cgroup memory limit".to_string());
    }
    value
        .parse::<u64>()
        .map(Some)
        .map_err(|_| "Linux cgroup memory limit is not a decimal u64 or 'max'".to_string())
}

#[cfg(target_os = "linux")]
fn linux_visible_cgroup_limit_with<F>(
    directory: &Path,
    mount_root: &Path,
    limit_name: &str,
    mut read: F,
) -> Result<Option<u64>, String>
where
    F: FnMut(&Path) -> Result<Option<String>, String>,
{
    // cgroup v2 legitimately omits memory.max at the real hierarchy root, but
    // a cgroup namespace can also present a constrained descendant as `/`.
    // mountinfo therefore cannot authenticate the exemption. Require the file
    // at every visible level and deny admission on either ambiguous case; that
    // trades Linux-host availability for never treating a missing visible
    // control file as proof of an unbounded hierarchy root. A tighter ancestor
    // hidden above the visible namespace remains the deployment TCB documented
    // at `machine_budget_bytes`. A future exception needs an authenticated
    // initial-namespace proof.
    let mut effective: Option<u64> = None;
    let mut saw_mount_root = false;
    for (depth, ancestor) in directory.ancestors().enumerate() {
        if depth >= MAX_CGROUP_ANCESTORS {
            return Err(format!("current memory cgroup exceeds {MAX_CGROUP_ANCESTORS} ancestors"));
        }
        if !ancestor.starts_with(mount_root) {
            break;
        }
        let control = ancestor.join(limit_name);
        match read(&control)? {
            Some(contents) => {
                if let Some(limit) = parse_linux_memory_limit(&contents)? {
                    effective = Some(effective.map_or(limit, |current| current.min(limit)));
                }
            }
            None => {
                return Err(format!(
                    "Linux cgroup memory authority is missing at a visible level: {}",
                    control.display()
                ));
            }
        }
        if ancestor == mount_root {
            saw_mount_root = true;
            break;
        }
    }
    if !saw_mount_root {
        return Err("current memory cgroup escaped its mounted authority".to_string());
    }
    Ok(effective)
}

#[cfg(target_os = "linux")]
fn linux_cgroup_memory_limit_bytes() -> Result<Option<u64>, String> {
    let cgroup = read_bounded_linux_control(Path::new("/proc/self/cgroup"))?;
    let memberships = parse_linux_cgroup_memberships(&cgroup)?;
    if memberships.unified.is_none() && memberships.v1_memory.is_none() {
        return Ok(None);
    }
    let mountinfo = read_bounded_linux_control(Path::new("/proc/self/mountinfo"))?;
    let (membership, unified, limit_name) = match (memberships.unified, memberships.v1_memory) {
        (Some(path), _) => (path, true, "memory.max"),
        (None, Some(path)) => (path, false, "memory.limit_in_bytes"),
        (None, None) => return Ok(None),
    };
    let (directory, mount_root) = linux_cgroup_directory(&mountinfo, &membership, unified)?
        .ok_or_else(|| "current memory cgroup has no matching mounted authority".to_string())?;
    linux_visible_cgroup_limit_with(
        &directory,
        &mount_root,
        limit_name,
        read_bounded_linux_control_optional,
    )
}

#[cfg(target_os = "linux")]
fn apply_linux_memory_limit(host_bytes: u64, limit: Result<Option<u64>, String>) -> u64 {
    match limit {
        Ok(Some(limit)) => host_bytes.min(limit),
        Ok(None) => host_bytes,
        // A present-but-unreadable/malformed Linux memory authority is not a
        // license to assume the larger host total inside a constrained domain.
        Err(_) => 0,
    }
}

#[cfg(target_os = "linux")]
fn total_physical_memory_bytes() -> u64 {
    // SAFETY: `_SC_PHYS_PAGES` / `_SC_PAGE_SIZE` are read-only sysconf queries
    // with no pointer parameters; they return -1 on failure (handled below).
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGE_SIZE) };
    if pages <= 0 || page_size <= 0 {
        return 0;
    }
    let Some(host_bytes) = (pages as u64).checked_mul(page_size as u64) else {
        return 0;
    };
    apply_linux_memory_limit(host_bytes, linux_cgroup_memory_limit_bytes())
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn total_physical_memory_bytes() -> u64 {
    0
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use std::os::unix::ffi::OsStrExt as _;
    #[cfg(unix)]
    use std::os::unix::fs::{PermissionsExt as _, symlink};

    use super::*;

    static FIXTURE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

    struct ScopedEnv {
        name: &'static str,
        previous: Option<std::ffi::OsString>,
    }

    impl ScopedEnv {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn set(name: &'static str, value: &str) -> Self {
            let previous = std::env::var_os(name);
            unsafe { std::env::set_var(name, value) };
            Self { name, previous }
        }
    }

    impl Drop for ScopedEnv {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn drop(&mut self) {
            match &self.previous {
                Some(value) => unsafe { std::env::set_var(self.name, value) },
                None => unsafe { std::env::remove_var(self.name) },
            }
        }
    }

    struct TestDirectory {
        path: PathBuf,
    }

    impl TestDirectory {
        fn new(label: &str) -> Self {
            let base = std::env::current_dir()
                .expect("test cwd")
                .join("target")
                .join("trust-memory-jobserver-tests");
            std::fs::create_dir_all(&base).expect("create memory-jobserver test root");
            #[cfg(unix)]
            std::fs::set_permissions(&base, std::fs::Permissions::from_mode(0o700))
                .expect("make memory-jobserver test root private");

            let sequence = FIXTURE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
            let epoch_nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|duration| duration.as_nanos())
                .unwrap_or(0);
            let path =
                base.join(format!("{label}-{}-{epoch_nanos}-{sequence}", std::process::id()));
            std::fs::create_dir(&path).expect("create unique memory-jobserver fixture");
            #[cfg(unix)]
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))
                .expect("make memory-jobserver fixture private");
            Self { path }
        }

        fn token_path(&self) -> PathBuf {
            self.path.join("memory.tokens")
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }

    fn write_private(path: &Path, bytes: &[u8]) {
        std::fs::write(path, bytes).expect("write private test file");
        #[cfg(unix)]
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
            .expect("make test file private");
    }

    fn write_private_ledger(path: &Path, bytes: &[u8]) {
        #[cfg(target_os = "linux")]
        {
            let canonical = authoritative_token_path(path).expect("authorize test ledger");
            let lock = AuthoritativeLock::acquire(
                &canonical,
                AdmissionWindow::new(Duration::from_secs(1)),
            )
            .expect("initialize test ledger PID-namespace marker while ledger is empty");
            drop(lock);
        }
        write_private(path, bytes);
    }

    #[test]
    fn machine_budget_is_fraction_of_total() {
        let total = total_physical_memory_bytes();
        // BUDGET cache may be set by another test; clear it for a clean read.
        BUDGET_BYTES_CACHE.store(0, Ordering::Relaxed);
        let budget = machine_budget_bytes();
        if total > 0 {
            assert!(budget > 0, "budget must be derivable when total RAM is known");
            assert!(budget < total, "budget must leave headroom below total RAM");
            // Exact integer fraction, rounded down without floating-point drift.
            let expected = ((u128::from(total) * u128::from(DEFAULT_BUDGET_NUMERATOR))
                / u128::from(DEFAULT_BUDGET_DENOMINATOR)) as u64;
            assert_eq!(budget, expected);
        }
    }

    #[test]
    fn per_job_limit_never_turns_a_configured_tiny_budget_into_zero() {
        assert_eq!(per_job_limit_mb_for(0, 1), None);
        assert_eq!(per_job_limit_mb_for(1024 * 1024 - 1, 1), None);
        assert_eq!(per_job_limit_mb_for(1024 * 1024, 1), Some(1));
        assert_eq!(per_job_limit_mb_for(4 * 1024 * 1024 * 1024, 16), Some(1024));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn linux_cgroup_membership_parser_selects_unified_and_memory_v1() {
        let memberships = parse_linux_cgroup_memberships(
            "0::/user.slice/trust.scope\n7:cpu,memory:/legacy/trust\n8:cpuset:/ignored\n",
        )
        .expect("parse bounded cgroup membership fixture");
        assert_eq!(memberships.unified.as_deref(), Some(Path::new("/user.slice/trust.scope")));
        assert_eq!(memberships.v1_memory.as_deref(), Some(Path::new("/legacy/trust")));
        assert!(parse_linux_cgroup_memberships("0::../../escape\n").is_err());
        assert!(parse_linux_cgroup_memberships("malformed\n").is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn linux_cgroup_mount_parser_maps_membership_under_mount_root() {
        let unified_mountinfo = concat!(
            "29 23 0:26 /user.slice /sys/fs/cgroup rw,nosuid,nodev,noexec,relatime - ",
            "cgroup2 cgroup rw\n"
        );
        let (directory, root) =
            linux_cgroup_directory(unified_mountinfo, Path::new("/user.slice/trust.scope"), true)
                .expect("parse unified mountinfo")
                .expect("find unified mount");
        assert_eq!(directory, Path::new("/sys/fs/cgroup/trust.scope"));
        assert_eq!(root, Path::new("/sys/fs/cgroup"));

        let legacy_mountinfo = concat!(
            "30 23 0:27 / /sys/fs/cgroup/memory rw,nosuid,nodev,noexec,relatime - ",
            "cgroup cgroup rw,memory\n"
        );
        let (directory, root) =
            linux_cgroup_directory(legacy_mountinfo, Path::new("/legacy/trust"), false)
                .expect("parse v1 mountinfo")
                .expect("find v1 memory mount");
        assert_eq!(directory, Path::new("/sys/fs/cgroup/memory/legacy/trust"));
        assert_eq!(root, Path::new("/sys/fs/cgroup/memory"));
        assert_eq!(
            decode_mountinfo_path(r"/sys/fs/cgroup/team\040space").expect("decode mount escape"),
            Path::new("/sys/fs/cgroup/team space")
        );
        assert!(decode_mountinfo_path(r"/sys/fs/cgroup/invalid\777").is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn linux_cgroup_limit_parser_is_exact_and_overflow_safe() {
        assert_eq!(parse_linux_memory_limit("max\n").expect("parse max"), None);
        assert_eq!(
            parse_linux_memory_limit("1073741824\n").expect("parse numeric cap"),
            Some(1_073_741_824)
        );
        assert_eq!(parse_linux_memory_limit("0").expect("zero is a real cap"), Some(0));
        assert!(parse_linux_memory_limit("1 2").is_err());
        assert!(parse_linux_memory_limit("18446744073709551616").is_err());
        assert_eq!(apply_linux_memory_limit(8_000, Ok(Some(2_000))), 2_000);
        assert_eq!(apply_linux_memory_limit(8_000, Ok(Some(16_000))), 8_000);
        assert_eq!(apply_linux_memory_limit(8_000, Ok(None)), 8_000);
        assert_eq!(apply_linux_memory_limit(8_000, Err("unreadable".to_string())), 0);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn linux_cgroup_v2_missing_limit_at_any_visible_level_fails_closed() {
        let root = Path::new("/fixture-cgroup");
        let missing_visible_root =
            linux_visible_cgroup_limit_with(root, root, "memory.max", |_| Ok(None));
        assert!(
            missing_visible_root.is_err(),
            "a `/` mount view does not authenticate the initial hierarchy root"
        );

        let child = root.join("child");
        let missing_child = linux_visible_cgroup_limit_with(&child, root, "memory.max", |path| {
            if path == child.join("memory.max") { Ok(None) } else { Ok(Some("max\n".to_string())) }
        });
        assert!(missing_child.is_err(), "a missing non-root limit must fail closed");

        let bounded =
            linux_visible_cgroup_limit_with(&child, root, "memory.max", |path| {
                match path.strip_prefix(root).expect("fixture path under root") {
                    relative if relative == Path::new("child/memory.max") => {
                        Ok(Some("2048\n".to_string()))
                    }
                    relative if relative == Path::new("memory.max") => {
                        Ok(Some("1024\n".to_string()))
                    }
                    relative => Err(format!("unexpected fixture read: {}", relative.display())),
                }
            })
            .expect("all visible limits are exact and readable");
        assert_eq!(bounded, Some(1024), "the tightest visible ancestor wins");
    }

    #[test]
    fn inert_reservation_is_noop() {
        let r = MemoryReservation::inert();
        assert!(!r.is_active());
        assert_eq!(r.bytes(), 0);
        // Dropping an inert reservation must not touch any file.
        drop(r);
    }

    #[test]
    fn zero_request_is_inert() {
        let r = acquire(0).expect("zero-byte acquisition is always inert");
        assert!(!r.is_active(), "a zero-byte request reserves nothing");
    }

    #[test]
    fn no_coordinator_acquire_is_inert() {
        // With TOKEN_FILE_ENV unset, acquire is a drop-in no-op regardless of size.
        // (The test process does not set the env; if a parallel test did, this is
        // still sound because an active reservation is also a valid outcome.)
        if std::env::var_os(TOKEN_FILE_ENV).is_none() {
            let r = acquire(1024 * 1024).expect("unconfigured acquisition is inert");
            assert!(!r.is_active(), "no token file ⇒ inert reservation (drop-in)");
        }
    }

    #[test]
    fn explicitly_empty_coordinator_path_fails_closed() {
        super::set_test_token_path(Some(PathBuf::new()));
        assert!(is_active(), "presence selects the file authority even when malformed");
        let error = acquire(1).expect_err("an empty configured authority must not become inert");
        assert!(error.to_string().contains("configured with an empty path"));
        assert!(
            acquire(0).is_err(),
            "a zero-byte request must not launder a malformed configured path"
        );
        super::set_test_token_path(None);
    }

    #[cfg(unix)]
    #[test]
    fn relative_authority_is_rejected_before_retry_or_drop_can_follow_cwd() {
        let relative = Path::new("relative-ledger/memory.tokens");
        let error = authoritative_token_path(relative)
            .expect_err("a process-wide cwd change must not redirect the authority");
        assert!(error.to_string().contains("token path must be absolute"));
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_parent_cannot_split_retries_across_ledgers() {
        let fixture = TestDirectory::new("symlinked-parent-authority");
        let actual_parent = fixture.path.join("actual");
        std::fs::create_dir(&actual_parent).expect("create actual ledger parent");
        std::fs::set_permissions(&actual_parent, std::fs::Permissions::from_mode(0o700))
            .expect("make actual parent private");
        let alias_parent = fixture.path.join("mutable-alias");
        symlink(&actual_parent, &alias_parent).expect("create mutable parent alias");
        let aliased_token = alias_parent.join("memory.tokens");

        let error = authoritative_token_path(&aliased_token)
            .expect_err("a mutable alias must not choose the ledger independently per retry");
        assert!(error.to_string().contains("must already be canonical"));
        assert!(!actual_parent.join("memory.tokens.lock").exists());

        let dotted = PathBuf::from(format!("{}/./memory.tokens", fixture.path.display()));
        assert!(
            authoritative_token_path(&dotted).is_err(),
            "lexical dot aliases must not select a second spelling"
        );
        let trailing = PathBuf::from(format!("{}/memory.tokens/", fixture.path.display()));
        assert!(
            authoritative_token_path(&trailing).is_err(),
            "a trailing-separator leaf alias must not be normalized silently"
        );
    }

    #[cfg(unix)]
    #[test]
    fn reservation_drop_uses_frozen_authority_not_current_environment() {
        let original = TestDirectory::new("frozen-drop-original");
        let replacement = TestDirectory::new("frozen-drop-replacement");
        let original_path = original.token_path();
        let replacement_path = replacement.token_path();
        super::set_test_token_path(Some(original_path.clone()));

        if total_physical_memory_bytes() == 0 {
            super::set_test_token_path(None);
            return;
        }
        let reservation = acquire(1).expect("reserve against the original absolute authority");
        assert_eq!(
            reservation.path.as_deref(),
            Some(original_path.as_path()),
            "acquire must retain the resolved absolute path"
        );

        // Environment changes after acquisition do not redirect Drop. This is
        // the same lifetime boundary at which a relative path plus chdir used to
        // release from an unrelated ledger.
        super::set_test_token_path(Some(replacement_path.clone()));
        drop(reservation);
        let (lines, _) = read_token_file(&original_path).expect("read released original ledger");
        assert!(lines.is_empty(), "Drop must remove the original reservation row");
        assert!(
            !replacement_path.exists(),
            "Drop must not create or edit the newly selected environment path"
        );
        super::set_test_token_path(None);
    }

    #[test]
    fn token_line_roundtrips() {
        let l = TokenLine { pid: 4321, bytes: 1 << 30, ts: 1_700_000_000 };
        let parsed = TokenLine::parse(&l.render()).expect("roundtrip");
        assert_eq!(parsed.pid, l.pid);
        assert_eq!(parsed.bytes, l.bytes);
        assert_eq!(parsed.ts, l.ts);
        // Malformed lines are errors, never silently ignored.
        assert!(TokenLine::parse("garbage").is_err());
        assert!(TokenLine::parse("12 notanumber 34").is_err());
        assert!(TokenLine::parse("12 34 56 extra").is_err());
        assert!(TokenLine::parse(" 12 34 56").is_err());
        assert!(TokenLine::parse("12  34 56").is_err());
        assert!(TokenLine::parse("012 34 56").is_err());
        assert!(TokenLine::parse("12 34 56\r").is_err());
        assert!(TokenLine::parse("0 34 56").is_err());
        assert!(TokenLine::parse("12 0 56").is_err());
        assert!(TokenLine::parse("12 34 0").is_err());
        assert!(TokenLine::parse("12 18446744073709551616 56").is_err());
    }

    #[test]
    fn prune_drops_only_dead_lines_and_keeps_old_live_work() {
        let now = 2_000_000_000u64;
        let mut lines = vec![
            // Our own live PID, fresh ⇒ kept.
            TokenLine { pid: std::process::id(), bytes: 100, ts: now },
            // Fresh timestamp but a PID that is certainly dead (1 is init/launchd,
            // but pid u32::MAX is not a live process) ⇒ pruned.
            TokenLine { pid: u32::MAX, bytes: 200, ts: now },
            // Our PID with an arbitrarily old timestamp ⇒ still kept. Age alone
            // cannot erase a legitimate long-running solver's reservation.
            TokenLine { pid: std::process::id(), bytes: 400, ts: 1 },
        ];
        prune_dead(&mut lines);
        let total: u64 = lines.iter().map(|l| l.bytes).sum();
        assert_eq!(total, 500, "both live reservations survive regardless of age");
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn lowered_budget_prunes_dead_formerly_valid_oversized_row_before_rejecting() {
        let fixture = TestDirectory::new("lowered-budget-dead-row");
        let path = fixture.token_path();
        let dead_pid = i32::MAX as u32;
        assert!(!pid_is_alive(dead_pid), "fixture PID must be definitely absent");
        let now = unix_now().max(1);
        write_private_ledger(&path, format!("{dead_pid} 4096 {now}").as_bytes());

        let admitted = try_admit(
            &path,
            std::process::id(),
            512,
            1024,
            AdmissionWindow::new(Duration::from_secs(1)),
        )
        .expect("a dead row above the newly lowered budget is reclaimable");
        assert!(admitted);
        let (lines, _) = read_token_file(&path).expect("read rewritten lowered-budget ledger");
        assert_eq!(lines.len(), 1);
        assert_eq!(lines[0].pid, std::process::id());
        assert_eq!(lines[0].bytes, 512);
    }

    #[cfg(unix)]
    #[test]
    fn pid_mismatched_drop_simulating_post_fork_child_retains_parent_row() {
        let fixture = TestDirectory::new("post-fork-child-drop");
        let path = fixture.token_path();
        let current = std::process::id();
        let recorded_pid = if current < i32::MAX as u32 { current + 1 } else { current - 1 };
        let bytes = 4096;
        let body = format!("{recorded_pid} {bytes} {}", unix_now().max(1));
        write_private(&path, body.as_bytes());

        drop(MemoryReservation { bytes, path: Some(path.clone()), pid: recorded_pid });
        assert_eq!(
            std::fs::read_to_string(&path).expect("read retained parent row"),
            body,
            "a child PID must not release the recorded parent's reservation"
        );
        assert!(
            !lock_path_for(&path).exists(),
            "PID mismatch must return before touching coordination state"
        );
    }

    #[test]
    fn end_to_end_reserve_and_release_under_token_file() {
        let _env = super::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let fixture = TestDirectory::new("reserve-release");
        let path = fixture.token_path();
        // Per-thread token-path override (NOT the process-global env): isolates
        // this test's bucket from every other parallel test's acquire/reserved.
        super::set_test_token_path(Some(path.clone()));
        BUDGET_BYTES_CACHE.store(0, Ordering::Relaxed);

        let total = total_physical_memory_bytes();
        if total > 0 {
            // A tiny request must be granted, and reserved_bytes must reflect it.
            let r = acquire(1024 * 1024).expect("admit a tiny request");
            assert!(r.is_active(), "a 1 MiB request must fit the machine budget");
            assert_eq!(reserved_bytes().expect("read live reservation"), 1024 * 1024);
            drop(r);
            // After release the bucket is empty again.
            assert_eq!(
                reserved_bytes().expect("read released ledger"),
                0,
                "dropping the reservation frees its bytes"
            );

            // A request larger than the whole budget can NEVER fit, so it
            // fails closed IMMEDIATELY — no peer release could ever satisfy it.
            assert!(matches!(
                acquire(u64::MAX),
                Err(MemoryJobserverError::RequestExceedsBudget { .. })
            ));
            assert_eq!(
                reserved_bytes().expect("read ledger after refused request"),
                0,
                "a refused acquire reserves nothing"
            );
        }

        super::set_test_token_path(None);
        BUDGET_BYTES_CACHE.store(0, Ordering::Relaxed);
    }

    #[test]
    fn over_budget_acquire_blocks_until_deadline_then_fails_closed() {
        let _env = super::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // A request that fits the budget on its own but does NOT fit alongside an
        // already-held reservation must BLOCK up to the (short, env-overridden)
        // deadline and then fail — bounded, never a deadlock or unreserved spawn.
        let fixture = TestDirectory::new("budget-deadline");
        let path = fixture.token_path();
        // Per-thread token-path override (NOT the process-global env) isolates
        // this test's bucket; the deadline env is global but only shortens timing.
        super::set_test_token_path(Some(path.clone()));
        let _deadline = ScopedEnv::set(ACQUIRE_DEADLINE_ENV, "150"); // 150 ms cap.
        BUDGET_BYTES_CACHE.store(0, Ordering::Relaxed);

        let budget = machine_budget_bytes();
        if budget > 0 {
            // Hold a reservation for the FULL budget so any further request must
            // wait. Sized just under the budget so it is itself grantable.
            let big = acquire(budget).expect("admit whole-budget reservation");
            assert!(big.is_active(), "the whole-budget request must be granted first");

            // A second (fits-alone) request cannot fit now; it should block for
            // ~the deadline, then error. Verify it took at least most of the
            // deadline (proving it blocked, not busy-failed instantly).
            let t0 = Instant::now();
            let blocked = acquire(budget / 2).expect_err("full bucket must fail at deadline");
            let waited = t0.elapsed();
            assert!(
                matches!(blocked, MemoryJobserverError::AdmissionDeadline { .. }),
                "a request over the live budget must report deadline expiry"
            );
            assert!(
                waited >= Duration::from_millis(100),
                "acquire must BLOCK (slept) near the deadline, waited only {waited:?}"
            );

            // Releasing the holder frees the budget; a fresh acquire admits at
            // once (a parked waiter would have been admitted the same way).
            drop(big);
            let after = acquire(budget / 2).expect("admit after release");
            assert!(after.is_active(), "after release, the request fits and is admitted");
            drop(after);
            assert_eq!(
                reserved_bytes().expect("read empty bucket"),
                0,
                "bucket empty after all reservations drop"
            );
        }

        super::set_test_token_path(None);
        BUDGET_BYTES_CACHE.store(0, Ordering::Relaxed);
    }

    #[cfg(unix)]
    #[test]
    fn malformed_ledger_rows_are_rejected_instead_of_filtered_out() {
        let fixture = TestDirectory::new("malformed-ledger");
        let path = fixture.token_path();
        let now = unix_now().max(1);
        let pid = std::process::id();

        for body in [
            format!("{pid} 1 {now} extra"),
            format!("0 1 {now}"),
            format!("{pid} 0 {now}"),
            format!("{pid} 1 0"),
            format!("{pid} 18446744073709551616 {now}"),
            format!(" {pid} 1 {now}"),
            format!("{pid}  1 {now}"),
            format!("{pid} 1 {now}\n"),
            format!("{pid} 1 {now}\r\n"),
            "not a token row".to_string(),
        ] {
            write_private_ledger(&path, body.as_bytes());
            let error = rewrite_tokens(&path, |_| Ok(())).expect_err("malformed row must fail");
            assert!(
                error.to_string().contains("malformed token ledger row"),
                "unexpected error for {body:?}: {error}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn invalid_utf8_ledger_is_an_error_not_an_empty_bucket() {
        let fixture = TestDirectory::new("invalid-utf8");
        let path = fixture.token_path();
        write_private_ledger(&path, &[0xff, 0xfe, 0xfd]);
        let error = rewrite_tokens(&path, |_| Ok(())).expect_err("invalid UTF-8 must fail");
        assert!(error.to_string().contains("not UTF-8"), "unexpected error: {error}");
    }

    #[test]
    fn ledger_read_errors_propagate() {
        struct FailingReader;

        impl Read for FailingReader {
            fn read(&mut self, _buffer: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::new(
                    std::io::ErrorKind::PermissionDenied,
                    "injected ledger read denial",
                ))
            }
        }

        let error = read_and_parse_token_ledger(FailingReader, Path::new("injected.tokens"))
            .expect_err("read denial must propagate");
        let rendered = error.to_string();
        assert!(rendered.contains("cannot read token ledger"), "unexpected error: {rendered}");
        assert!(rendered.contains("injected ledger read denial"));
    }

    #[cfg(unix)]
    #[test]
    fn non_regular_ledger_path_is_not_treated_as_not_found() {
        let fixture = TestDirectory::new("ledger-directory");
        let path = fixture.token_path();
        std::fs::create_dir(&path).expect("preplant directory at ledger path");

        let error = rewrite_tokens(&path, |_| Ok(())).expect_err("directory ledger must fail");
        assert!(error.to_string().contains("not a regular file"), "unexpected error: {error}");
        assert!(path.is_dir(), "failed admission must preserve the preplanted directory");
    }

    #[cfg(unix)]
    #[test]
    fn fifo_ledger_is_rejected_without_blocking_on_open() {
        let fixture = TestDirectory::new("ledger-fifo");
        let path = fixture.token_path();
        let encoded =
            std::ffi::CString::new(path.as_os_str().as_bytes()).expect("FIFO path CString");
        // SAFETY: `encoded` is a live NUL-terminated pathname and mode contains
        // only ordinary permission bits. The unique fixture path is absent.
        assert_eq!(unsafe { libc::mkfifo(encoded.as_ptr(), 0o600) }, 0, "create ledger FIFO");

        let started = Instant::now();
        let error =
            rewrite_tokens_until(&path, AdmissionWindow::new(Duration::from_millis(100)), |_| {
                Ok(())
            })
            .expect_err("FIFO ledger must fail regular-file validation");
        assert!(error.to_string().contains("not a regular file"));
        assert!(
            started.elapsed() < Duration::from_secs(2),
            "opening a FIFO must not wedge before validation"
        );
    }

    #[cfg(unix)]
    #[test]
    fn aggregate_overflow_is_rejected_before_dead_owner_pruning() {
        let fixture = TestDirectory::new("aggregate-overflow");
        let path = fixture.token_path();
        let now = unix_now().max(1);
        let pid = std::process::id();
        write_private_ledger(&path, format!("{pid} {} {now}\n{pid} 1 {now}", u64::MAX).as_bytes());

        let error = rewrite_tokens(&path, |lines| {
            // Even a no-op edit must not launder a pre-existing wrapped total.
            let _ = lines;
            Ok(())
        })
        .expect_err("aggregate overflow must fail");
        assert!(error.to_string().contains("aggregation overflowed"));
    }

    #[cfg(unix)]
    #[test]
    fn predictable_legacy_temp_symlink_is_never_followed_or_removed() {
        let fixture = TestDirectory::new("legacy-temp-symlink");
        let path = fixture.token_path();
        let victim = fixture.path.join("victim");
        write_private(&victim, b"do not modify");
        let legacy_temporary = path.with_extension("tmp");
        symlink(&victim, &legacy_temporary).expect("preplant legacy temporary symlink");

        rewrite_tokens(&path, |_| Ok(())).expect("secure random temporary must ignore legacy name");
        assert_eq!(std::fs::read(&victim).expect("read victim"), b"do not modify");
        assert!(
            std::fs::symlink_metadata(&legacy_temporary)
                .expect("legacy symlink preserved")
                .file_type()
                .is_symlink()
        );
    }

    #[cfg(unix)]
    #[test]
    fn destination_symlink_is_rejected_without_clobbering_it_or_its_target() {
        let fixture = TestDirectory::new("destination-symlink");
        let path = fixture.token_path();
        let victim = fixture.path.join("victim");
        write_private(&victim, b"authoritative victim");
        symlink(&victim, &path).expect("preplant destination symlink");

        let error = rewrite_tokens(&path, |_| Ok(())).expect_err("destination symlink must fail");
        assert!(
            error.to_string().contains("token ledger")
                || error.to_string().contains("Too many levels"),
            "unexpected error: {error}"
        );
        assert_eq!(std::fs::read(&victim).expect("read victim"), b"authoritative victim");
        assert!(
            std::fs::symlink_metadata(&path)
                .expect("destination symlink preserved")
                .file_type()
                .is_symlink()
        );
    }

    #[cfg(unix)]
    #[test]
    fn permissive_ledger_and_lock_files_are_rejected() {
        let ledger_fixture = TestDirectory::new("permissive-ledger");
        let ledger = ledger_fixture.token_path();
        std::fs::write(&ledger, b"").expect("write permissive ledger");
        std::fs::set_permissions(&ledger, std::fs::Permissions::from_mode(0o644))
            .expect("make ledger permissive");
        let error = rewrite_tokens(&ledger, |_| Ok(())).expect_err("permissive ledger must fail");
        assert!(error.to_string().contains("grants group/other permissions"));

        let lock_fixture = TestDirectory::new("permissive-lock");
        let token = lock_fixture.token_path();
        let lock = lock_path_for(&token);
        std::fs::write(&lock, b"").expect("write permissive lock");
        std::fs::set_permissions(&lock, std::fs::Permissions::from_mode(0o644))
            .expect("make lock permissive");
        let error = rewrite_tokens(&token, |_| Ok(())).expect_err("permissive lock must fail");
        assert!(error.to_string().contains("grants group/other permissions"));
    }

    #[cfg(unix)]
    #[test]
    fn writable_ancestor_is_rejected_even_with_a_private_leaf_parent() {
        let fixture = TestDirectory::new("writable-ancestor");
        let shared = fixture.path.join("shared");
        let private_parent = shared.join("private");
        std::fs::create_dir(&shared).expect("create shared ancestor");
        std::fs::create_dir(&private_parent).expect("create private leaf parent");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o777))
            .expect("make ancestor writable");
        std::fs::set_permissions(&private_parent, std::fs::Permissions::from_mode(0o700))
            .expect("keep leaf parent private");
        let path = private_parent.join("memory.tokens");

        let error = rewrite_tokens(&path, |_| Ok(())).expect_err("writable ancestor must fail");
        assert!(error.to_string().contains("ancestor is group/other writable"));
        assert!(!lock_path_for(&path).exists(), "no lock may be created below an unsafe chain");

        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o700))
            .expect("restore ancestor for cleanup");
    }

    #[cfg(unix)]
    #[test]
    fn lock_replacement_after_acquisition_is_detected_before_ledger_read() {
        let fixture = TestDirectory::new("lock-replacement");
        let path = fixture.token_path();
        let error = rewrite_tokens_with_hook(
            &path,
            |_| Ok(()),
            |lock_path| {
                std::fs::remove_file(lock_path).map_err(|error| {
                    ledger_error(format!("cannot remove test lock sentinel: {error}"))
                })?;
                write_private(lock_path, b"replacement");
                Ok(())
            },
        )
        .expect_err("replacement of the locked inode must fail");
        assert!(
            error.to_string().contains("memory-jobserver lock sentinel"),
            "unexpected error: {error}"
        );
        assert!(!path.exists(), "ledger read/publication must not begin after lock replacement");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn lock_domain_marker_rejects_a_different_pid_namespace_authority() {
        let fixture = TestDirectory::new("pid-namespace-domain");
        let path = authoritative_token_path(&fixture.token_path()).expect("authorize fixture");
        let lock =
            AuthoritativeLock::acquire(&path, AdmissionWindow::new(Duration::from_millis(100)))
                .expect("initialize PID-namespace marker");
        let lock_path = lock.path().to_path_buf();
        drop(lock);
        assert_eq!(
            std::fs::read_to_string(&lock_path).expect("read initialized marker"),
            linux_pid_namespace_marker().expect("derive current namespace marker")
        );

        write_private(&lock_path, b"trust-memory-jobserver-lock-v1 pidns=0:1\n");
        let error = rewrite_tokens(&path, |_| Ok(()))
            .expect_err("a different PID namespace marker must fail before ledger access");
        assert!(error.to_string().contains("does not match this Linux PID namespace"));
        assert!(!path.exists());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn empty_lock_domain_marker_never_adopts_a_nonempty_ledger() {
        let fixture = TestDirectory::new("pid-namespace-no-adoption");
        let path = fixture.token_path();
        let body = format!("{} 4096 {}", std::process::id(), unix_now().max(1));
        // Deliberately bypass `write_private_ledger`: this models a restored or
        // legacy nonempty ledger whose lock marker is absent/empty.
        write_private(&path, body.as_bytes());

        let error = rewrite_tokens(&path, |_| Ok(()))
            .expect_err("an unstamped lock must not adopt live rows from another namespace");
        assert!(error.to_string().contains("refuses to adopt non-empty ledger"));
        assert_eq!(std::fs::read_to_string(&path).expect("ledger retained"), body);
        assert_eq!(
            std::fs::metadata(lock_path_for(&path)).expect("empty lock retained").len(),
            0,
            "failed adoption must not stamp the namespace marker"
        );
    }

    #[cfg(unix)]
    #[test]
    fn held_lock_obeys_the_absolute_admission_deadline() {
        let fixture = TestDirectory::new("held-lock-deadline");
        let path = authoritative_token_path(&fixture.token_path()).expect("authorize fixture");
        let holder =
            AuthoritativeLock::acquire(&path, AdmissionWindow::new(Duration::from_secs(1)))
                .expect("acquire held lock");

        let started = Instant::now();
        let error =
            rewrite_tokens_until(&path, AdmissionWindow::new(Duration::from_millis(100)), |_| {
                Ok(())
            })
            .expect_err("second acquisition must time out");
        let elapsed = started.elapsed();
        assert!(matches!(error, MemoryJobserverError::AdmissionDeadline { .. }));
        assert!(
            elapsed >= Duration::from_millis(75),
            "lock waiter returned too early: {elapsed:?}"
        );
        assert!(elapsed < Duration::from_secs(2), "lock waiter exceeded its bound: {elapsed:?}");
        drop(holder);
    }

    #[cfg(unix)]
    #[test]
    fn release_waits_through_brief_contention_and_removes_its_live_row() {
        let fixture = TestDirectory::new("release-contention");
        let path = fixture.token_path();
        let pid = std::process::id();
        let bytes = 4096;
        assert!(
            try_admit(&path, pid, bytes, bytes * 2, AdmissionWindow::new(Duration::from_secs(1)),)
                .expect("seed reservation row")
        );
        let reservation = MemoryReservation { bytes, path: Some(path.clone()), pid };

        let canonical = authoritative_token_path(&path).expect("authorize fixture");
        let (locked_tx, locked_rx) = std::sync::mpsc::channel();
        let holder = std::thread::spawn(move || {
            let lock = AuthoritativeLock::acquire(
                &canonical,
                AdmissionWindow::new(Duration::from_secs(1)),
            )
            .expect("hold ledger lock");
            locked_tx.send(()).expect("signal held lock");
            std::thread::sleep(Duration::from_millis(150));
            drop(lock);
        });
        locked_rx.recv_timeout(Duration::from_secs(1)).expect("wait for held lock");

        let started = Instant::now();
        drop(reservation);
        let elapsed = started.elapsed();
        holder.join().expect("join lock holder");
        assert!(elapsed >= Duration::from_millis(100), "release did not encounter contention");
        assert!(elapsed < Duration::from_secs(2), "release exceeded its finite bound: {elapsed:?}");

        let (lines, _) = read_token_file(&path).expect("read released ledger");
        assert!(lines.is_empty(), "brief contention must not leak the live process's row");
    }
}
