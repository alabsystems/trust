// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-10-17; do not grow casually
// Trust: client + shared server helpers for the `trustd` memory-coordination
// daemon — the in-memory live-authority version of the `memory_jobserver` flock
// token bucket that fixes the 2026-06-17 aggregate OOM (N concurrent `trustc`
// workers, no global budget, 143 GB on a 36 GB box).
//
// ARCHITECTURE. `memory_jobserver.rs` already solves the cross-process budget
// problem with an `fs2`-flocked token *file*. This module mirrors that admission
// algorithm with the token state held in RAM behind a `Mutex`/`Condvar` instead
// of on disk, reached over a Unix-domain socket — so it is faster (no per-acquire
// flock + temp-file rename), has true *blocking* admission with prompt wakeups
// instead of backoff-polling a file, and can serve a live `STATUS` to the
// menubar. Crucially it is OPTIONAL for standalone callers: it is a different
// *transport* with the same reserve/release model. When no daemon lane is
// provisioned, in-process callers may use the explicitly configured flock
// bucket, which itself is inert when raw `trustc` has no configured authority.
// An active file reservation cannot be transferred atomically to an external AY
// child and that spawn is rejected before exec; it is not a solver fallback.
// Once a socket lane is selected, transport/protocol failure is returned before
// solver spawn and never crosses into the independent file authority.
//
// This is the SINGLE seam both the in-process backend (now) and a future
// `compiler/` trustc edit (later) call — the x.py follow-on will call
// `coordinator::reserve()` with zero new wiring. Both the daemon binary
// (`bin/trustd.rs`) and the client live against the grammar/JSON defined here,
// reducing the surface on which their protocol implementations can drift.
//
// DEGRADATION LADDER:
//   1. No env (raw `trustc`)                  -> inert reservation (byte-identical to rustc)
//   2. SOCK env set & daemon reachable         -> daemon RESERVE/RELEASE (live authority)
//   3. SOCK lane unprovisioned, TOKEN env set  -> memory_jobserver::acquire() (flock bucket)
//   4. selected SOCK failure / ledger error    -> fail before solver spawn
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashSet;
#[cfg(unix)]
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
// Trust: the trustd memory-coordinator transport uses Unix-domain sockets, which
// std only exposes on Unix. On non-Unix hosts (Windows) the entire daemon
// transport is compiled out. Standalone unconfigured callers remain inert, but
// verified crate-mode orchestration must reject the platform before fan-out: its
// file authority cannot establish the Unix ownership/locking invariants. See
// the `#[cfg(unix)]` gates throughout this file.
#[cfg(unix)]
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;
#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
#[cfg(unix)]
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
#[cfg(unix)]
use sha2::{Digest, Sha256};

use crate::memory_jobserver::{
    self, MemoryJobserverError, MemoryReservation, acquire_deadline, machine_budget_bytes,
};

// Trust: trust-router unit tests include this file by `#[path]`, where a bare
// `mod admission;` would resolve beside it rather than under coordinator/.
#[path = "coordinator/admission.rs"]
mod admission;
pub use admission::{
    ADMISSION_GRANT_VERSION, ADMISSION_IDENTITY_VERSION, ADMISSION_RECEIPT_VERSION,
    ADMISSION_REQUEST_VERSION, AdmissionGrant, AdmissionIdentity, AdmissionReceipt, AdmissionWork,
    AdmissionWorkKind, EvidencedReservation,
};
#[cfg(unix)]
pub use admission::{reserve_with_evidence, reserve_with_evidence_at};

// ===========================================================================
// Wire-protocol constants (single source of truth for client AND daemon)
// ===========================================================================

/// Environment variable naming the daemon's Unix-domain socket. The orchestrator
/// (`targo` crate mode) sets this to one private per-euid host endpoint shared
/// across Cargo target directories.
/// UNSET ⇒ rung 2 is skipped and the worker falls straight to the file bucket.
/// Additive/opt-in by presence: a worker built before this change ignores it.
pub const SOCK_ENV: &str = "TRUST_MEMORY_JOBSERVER_SOCK";

/// A caller-chosen private directory that replaces the per-euid runtime root as
/// the home of the launcher's memory-authority endpoint (see
/// [`host_socket_path_in`]). Setting it opts a run OUT of the host-wide memory
/// domain: builds that share the directory share one budget, and builds outside
/// it do not see them. It exists so fake-toolchain tests can run a stub daemon
/// without touching — or being refused by — a real verified build's endpoint;
/// the launcher discloses every use, and the directory must satisfy the same
/// private-ownership rules as the default root.
pub const RUNTIME_DIR_ENV: &str = "TRUSTD_RUNTIME_DIR";

/// Force-refuse daemon startup (debug/CI). When set to `1`, `ensure_daemon`
/// returns [`EnsureDaemonError::Disabled`]. A caller may use the file lane only
/// when no socket domain is also configured; combining both fails closed to
/// prevent split authority.
pub const DISABLE_ENV: &str = "TRUSTD_DISABLE";

/// Schema tag embedded in every STATUS reply. The menubar parses this to confirm
/// it is talking to a compatible daemon.
pub const STATUS_VERSION: &str = "trustd.status.v1";

/// Closed schema for the build/runtime identity handshake. STATUS remains v1 so
/// observers do not need to understand release provenance; launchers require
/// this separate reply before reusing a pre-existing memory authority.
pub const IDENTITY_VERSION: &str = "trustd.identity.v1";

/// Maximum bytes accepted for a single request line. A longer line is rejected
/// (`ERR line-too-long`) to bound an unbounded-read DoS. Requests are tiny,
/// fixed-shape ASCII; 4 KiB is generous (`<label>` is capped at 128 anyway).
pub const MAX_REQUEST_BYTES: usize = 4096;

/// Maximum stored `<label>` length (bytes). Longer labels are truncated.
pub const MAX_LABEL_BYTES: usize = 128;

// Legacy provenance: the dead SMT-echo trustd bound 127.0.0.1:7878. We removed
// the `TcpListener` in favor of a private per-euid Unix socket (see module doc). The
// const is retained only as a comment so the port's history stays discoverable.
// const DEFAULT_PORT: u16 = 7878;

/// How often the standalone maintenance thread refreshes the production
/// host/cgroup ceiling. Grant lifetime is connection-owned, never inferred from
/// a client-supplied PID or age. STATUS is a pure snapshot.
pub(crate) const BUDGET_REFRESH_INTERVAL: Duration = Duration::from_secs(5);

/// Idle-shutdown bound: if `active` is empty, no session holds a lease (see
/// `DaemonLease`) AND no admission-affecting request has arrived for this
/// long, the daemon exits so a `targo`-spawned daemon does not outlive the
/// build. The lease is what bounds it by the build rather than by the gap
/// between two admissions: a unit may compile for longer than this before it
/// asks, and the session that exported this socket to it still needs the
/// daemon then. Its socket remains as a stale rendezvous entry for the next
/// stable-lock owner to reclaim. Observational STATUS/PING/IDENTITY traffic
/// intentionally does not extend this lifetime.
/// Callers outside this crate report this to operators: after a toolchain
/// promotion the PREVIOUS seal's daemon still owns the socket, and the only
/// correct remedy is to wait it out — this long after the last build holding
/// it ends. Publishing the number keeps that advice from drifting from the
/// behaviour.
pub const IDLE_TIMEOUT: Duration = Duration::from_secs(5 * 60);

/// Hard ceiling on live server connection threads. A normal build uses roughly
/// fourteen workers plus one observer, and every live verified session holds
/// one more, its lease, for its whole life (two for a moment while a
/// rewrite-loop iteration replaces the lease); 64 leaves ample headroom
/// without letting same-euid clients turn one Unix socket into an unbounded
/// thread allocator.
pub(crate) const MAX_SERVER_CONNECTIONS: usize = 64;

/// A newly accepted local client has ample time to send its first tiny frame,
/// but cannot occupy a handler indefinitely without speaking the protocol.
const SERVER_INITIAL_READ_TIMEOUT: Duration = Duration::from_secs(15);

/// Poll budget for `ensure_daemon` readiness after spawning `trustd`.
///
/// Process-level controls already allow three seconds for a freshly started
/// daemon. Give packaged startup a little more room for loaded CI hosts while
/// keeping the refusal absolutely bounded.
const SPAWN_READY_TIMEOUT: Duration = Duration::from_secs(5);
/// How long a launcher whose spawned `trustd` lost the stable-ownership race
/// ([`OWNED_ELSEWHERE`]) waits for the live owner's exact-identity lease.
///
/// The owner is alive (it holds the stable lock), so adopting it is the only
/// way this run can proceed; a probe bounded by [`OBSERVER_IO_TIMEOUT`] refused
/// a slow but healthy one. Measured 2026-10-27 on an 18-core host with ~69
/// runnable threads waiting for a core: an idle production daemon (nothing
/// reserved, nothing queued) took 2.7-7.9 s to answer one PING, two `pub stage`
/// gates exited 3 "another trustd owns", and a third adopted it in a quieter
/// moment.
///
/// The owner may also not have published yet: [`bind_owned_socket`] takes the
/// lock BEFORE it reclaims a stale socket and binds its own (and a first
/// sentinel's creator syncs the directory before that), so in that window the
/// path is missing or refuses the connection. The launcher re-probes every
/// [`SPAWN_POLL_INTERVAL`] through this window while the endpoint is not
/// serving ([`ProbeMiss::NotServing`]) or answers that it is at its connection
/// limit ([`ProbeMiss::Busy`]: `ERR busy`, a capacity answer that names no
/// identity, TRUSTD-LOST-RACE-2); the first definite answer
/// ([`ProbeMiss::Refused`]: a foreign identity, an unacceptable STATUS, a
/// refused lease, a closed exchange) still ends it, never retried into
/// adoption, and so does the owner releasing the lock without ever serving
/// ([`SpawnedDaemon::OwnerVanished`]). A refusal whose lock is free within
/// [`REFUSING_OWNER_RELEASE_GRACE`] came from an owner that died answering, and
/// costs one more spawn instead of the run.
const LIVE_OWNER_ADOPT_TIMEOUT: Duration = Duration::from_secs(60);
/// How long a launcher whose child lost the ownership race, and whose probe
/// was then refused, watches the stable lock before it reports the refusal.
///
/// An owner that published and then died before it answered (its startup
/// failed after the bind, or it exited idle while the probe sat in its listen
/// queue) refuses by closing the exchange, and releases the lock a moment
/// later: `OwnedSocket` drops its listener first, then its lock, and an owner
/// that answered a lease `DEGRADED` first syncs its CLEAN epoch. A free lock
/// means nothing will serve, so the launcher spawns once more
/// ([`SpawnedDaemon::OwnerVanished`]). NOT measured: it bounds an exit, and it
/// costs only a launcher refused by an owner that lives on (which then fails
/// as before, this much later). It never extends the adoption window.
const REFUSING_OWNER_RELEASE_GRACE: Duration = Duration::from_secs(2);
/// What a `trustd` that lost the stable-ownership race says
/// ([`try_lock_stable_sentinel`]); its launcher reads it from the child's stderr.
const OWNED_ELSEWHERE: &str = "another trustd owns";
/// Per-poll connect-attempt spacing while waiting for `trustd` to bind.
const SPAWN_POLL_INTERVAL: Duration = Duration::from_millis(20);
/// Maximum child-stderr bytes retained in a startup error. The reader keeps
/// draining after this bound so a verbose child cannot deadlock on a full pipe.
const MAX_SPAWN_STDERR_BYTES: usize = 16 * 1024;

/// Transport overhead allowed in addition to the admission wait itself. The
/// client uses one absolute deadline, so a responder cannot extend this bound by
/// trickling a reply one byte at a time.
const CLIENT_IO_MARGIN: Duration = Duration::from_millis(500);

/// STATUS/IDENTITY are observational and must finish promptly. This is also the
/// maximum connect budget used by the longer RESERVE exchange.
const OBSERVER_IO_TIMEOUT: Duration = Duration::from_millis(500);

/// Stable per-user runtime namespace. It deliberately does not live below a
/// Cargo target directory: every normal verified build for one euid must share
/// one admission domain, and `cargo clean` must not remove its rendezvous or
/// create another advisory-lock inode while the daemon is alive.
const LOCK_ROOT_PREFIX: &str = "trustd-runtime-locks";

/// Fixed endpoint inside the private per-euid runtime namespace. A fixed name
/// is the authority invariant: two concurrent builds with different target
/// directories cannot each mint 70% of the same host memory.
const HOST_SOCKET_NAME: &str = "trust-memory-jobserver.sock";

// ===========================================================================
// STATUS JSON schema (`trustd.status.v1`) — frozen field names/types
// ===========================================================================

/// Typed mirror of the STATUS JSON, for `status()`, the menubar, and tests.
/// Field names/types are frozen — the Swift menubar decodes the identical shape.
#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct DaemonStatus {
    /// Schema tag: [`STATUS_VERSION`].
    pub version: String,
    /// Monotonic effective-memory admission ceiling. Production daemons begin
    /// at `machine_budget_bytes()` and lower this value when their current
    /// cgroup/host observation shrinks; `0` ⇒ disabled.
    pub budget_bytes: u64,
    /// Σ active reservation bytes.
    pub reserved_bytes: u64,
    /// `budget_bytes.saturating_sub(reserved_bytes)`.
    pub free_bytes: u64,
    /// RESERVE waiters currently parked on admission.
    pub queue_depth: u64,
    /// Lifetime count of GRANTED replies (active grants only — `RESERVE 0`
    /// sentinel grants are not counted).
    pub granted_total: u64,
    /// Lifetime count of reservations freed (RELEASE or connection loss).
    pub released_total: u64,
    /// Daemon start, unix seconds.
    pub started_at: u64,
    /// One entry per live reservation, newest-last.
    pub active: Vec<ActiveReservation>,
}

/// One live reservation in [`DaemonStatus::active`].
#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct ActiveReservation {
    /// Worker pid reported by the client for diagnostics only. Grant lifetime
    /// is bound to the connection, not inferred with `kill(pid, 0)`.
    pub pid: u32,
    /// Reserved bytes.
    pub bytes: u64,
    /// Free-form tag (crate name / pid-purpose); `""` if none. `<=128` chars.
    pub label: String,
    /// `now - grant time`, seconds.
    pub since_secs: u64,
    /// The grant token (lets the UI correlate).
    pub token: u64,
}

/// Build and runtime identity returned by `IDENTITY`.
///
/// The schema is deliberately closed. A launcher compares every field, including
/// the SHA-256 of the executable the daemon itself is running, with the exact
/// packaged sibling it is about to spawn. A daemon from an older checkout can
/// therefore never be silently adopted merely because it also speaks STATUS v1.
#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct DaemonIdentity {
    /// Schema tag: [`IDENTITY_VERSION`].
    pub version: String,
    /// Admission/status protocol implemented by this process.
    pub protocol: String,
    /// Compiler/toolchain release embedded at build time.
    pub release: String,
    /// Repository commit embedded at build time, or `unbound` for local builds.
    pub commit: String,
    /// Lowercase SHA-256 of the executable bytes this process is running.
    pub executable_sha256: String,
}

/// Observation returned by a complete, live daemon protocol exercise.
///
/// This is deliberately produced only from an exact executable-bound endpoint:
/// callers cannot construct release evidence from a PING-only mock or from
/// independently fabricated STATUS snapshots.
#[cfg(unix)]
#[derive(Debug, Clone)]
pub struct DaemonSmoke {
    pub identity: DaemonIdentity,
    pub status_before: DaemonStatus,
    pub status_reserved: DaemonStatus,
    pub status_released: DaemonStatus,
    pub reservation_pid: u32,
    pub reservation_token: u64,
    pub reservation_bytes: u64,
    pub reservation_label: String,
}

impl DaemonIdentity {
    fn has_valid_invariants(&self) -> bool {
        self.version == IDENTITY_VERSION
            && self.protocol == STATUS_VERSION
            && !self.release.is_empty()
            && !self.commit.is_empty()
            && self.executable_sha256.len() == 64
            && self.executable_sha256.bytes().all(|byte| byte.is_ascii_hexdigit())
    }
}

fn compiled_release() -> &'static str {
    option_env!("CFG_RELEASE").unwrap_or(env!("CARGO_PKG_VERSION"))
}

fn compiled_commit() -> &'static str {
    option_env!("CFG_VER_HASH").filter(|value| !value.is_empty()).unwrap_or("unbound")
}

impl DaemonStatus {
    /// Validate all semantic invariants promised by the closed STATUS v1 schema.
    /// This is public so release diagnostics can reject well-typed but internally
    /// contradictory evidence without duplicating the authority's rules.
    #[must_use]
    pub fn is_semantically_valid(&self) -> bool {
        self.has_valid_invariants()
    }

    /// Check the semantic invariants promised by `trustd.status.v1`. Deserializing
    /// the right field names and types is not enough: an ambient or incompatible
    /// process must not pass readiness with internally contradictory counters.
    fn has_valid_invariants(&self) -> bool {
        // A runtime cgroup ceiling can fall below already-granted cooperative
        // work. Those grants remain accounted until release, while free=0
        // prevents any new admission. The documented saturating arithmetic is
        // therefore intentional; reserved>budget is a safe transient state,
        // not a contradictory snapshot.
        if self.version != STATUS_VERSION
            || self.free_bytes != self.budget_bytes.saturating_sub(self.reserved_bytes)
        {
            return false;
        }

        let Some(active_count) = u64::try_from(self.active.len()).ok() else {
            return false;
        };
        if self.granted_total.checked_sub(self.released_total) != Some(active_count) {
            return false;
        }

        let mut reserved_sum = 0u64;
        let mut tokens = HashSet::with_capacity(self.active.len());
        for reservation in &self.active {
            let Some(sum) = reserved_sum.checked_add(reservation.bytes) else {
                return false;
            };
            reserved_sum = sum;
            if reservation.bytes == 0
                || reservation.token == 0
                || reservation.label.len() > MAX_LABEL_BYTES
                || !tokens.insert(reservation.token)
            {
                return false;
            }
        }
        reserved_sum == self.reserved_bytes
    }
}

// ===========================================================================
// Server state (shared, lives behind one Arc<Daemon>)
// ===========================================================================

/// A single live in-memory reservation (server-side).
#[derive(Debug, Clone)]
pub(crate) struct ServerReservation {
    token: u64,
    pid: u32,
    bytes: u64,
    label: String,
    /// For `since_secs` in STATUS.
    granted_at: Instant,
    /// Unauthenticated claims retained only while this reservation is live.
    work: Option<AdmissionWork>,
}

/// The mutable budget state, guarded by [`Daemon::state`].
#[derive(Debug)]
pub(crate) struct Budget {
    budget_bytes: u64,
    reserved_bytes: u64,
    active: Vec<ServerReservation>,
    /// Monotonic token allocator. Starts at 1 (`0` = inert sentinel).
    next_token: u64,
    /// Sticky across legacy token wrap: evidence tokens must never be reused.
    evidence_tokens_exhausted: bool,
    granted_total: u64,
    released_total: u64,
    /// Parked RESERVE waiters.
    queue_depth: u64,
    /// Live session leases, at most one per connection. Not in STATUS (its v1
    /// schema is frozen); the idle proof reads it under this same lock.
    leases: u64,
    started_at: u64,
}

impl Budget {
    fn new(budget_bytes: u64) -> Self {
        Self {
            budget_bytes,
            reserved_bytes: 0,
            active: Vec::new(),
            next_token: 1,
            evidence_tokens_exhausted: false,
            granted_total: 0,
            released_total: 0,
            queue_depth: 0,
            leases: 0,
            started_at: unix_now(),
        }
    }

    /// Render a STATUS snapshot from the current authoritative state. The
    /// live connection guard owns grant reclamation; keeping this method
    /// read-only is what makes STATUS safe for polling observers.
    fn snapshot(&self) -> DaemonStatus {
        let now = Instant::now();
        let active = self
            .active
            .iter()
            .map(|r| ActiveReservation {
                pid: r.pid,
                bytes: r.bytes,
                label: r.label.clone(),
                since_secs: now.saturating_duration_since(r.granted_at).as_secs(),
                token: r.token,
            })
            .collect();
        DaemonStatus {
            version: STATUS_VERSION.to_string(),
            budget_bytes: self.budget_bytes,
            reserved_bytes: self.reserved_bytes,
            free_bytes: self.budget_bytes.saturating_sub(self.reserved_bytes),
            queue_depth: self.queue_depth,
            granted_total: self.granted_total,
            released_total: self.released_total,
            started_at: self.started_at,
            active,
        }
    }
}

/// The daemon: shared budget behind a `Mutex`, plus a `Condvar` signalled on
/// every RELEASE / reclaim so a parked RESERVE wakes promptly.
pub(crate) struct Daemon {
    state: Mutex<Budget>,
    admit: Condvar,
    identity: DaemonIdentity,
    /// Entropy failure disables only the opt-in evidence protocol.
    admission_identity: Option<AdmissionIdentity>,
    /// Production follows a monotonic series of current host/cgroup
    /// observations. Fixed test daemons never consult ambient machine state.
    budget_policy: BudgetPolicy,
    #[cfg(unix)]
    active_connections: AtomicUsize,
    /// Once set, no later RESERVE may mint a grant. The accept loop sets this
    /// while holding the empty ledger immediately before it records a durable
    /// clean epoch and exits.
    shutting_down: AtomicBool,
    /// Last admission-affecting request (for idle shutdown), unix seconds.
    /// STATUS/PING never update this clock.
    last_activity: Mutex<u64>,
    #[cfg(test)]
    refresh_test_gate: Mutex<Option<Arc<RefreshTestGate>>>,
}

#[cfg(test)]
struct RefreshTestGate {
    observed: std::sync::Barrier,
    resume: std::sync::Barrier,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BudgetPolicy {
    DynamicMachine,
    Fixed,
}

impl Daemon {
    /// Construct a daemon with the current effective-memory budget, using the
    /// same derivation as the file transport. The production ceiling is
    /// re-observed and may only decrease before later admissions.
    pub(crate) fn new(identity: DaemonIdentity) -> Arc<Self> {
        Self::with_budget_policy(machine_budget_bytes(), identity, BudgetPolicy::DynamicMachine)
    }

    /// Construct a daemon with an explicit budget (the production path passes
    /// `machine_budget_bytes()`; tests pass a fixed value).
    pub(crate) fn with_budget(budget_bytes: u64) -> Arc<Self> {
        let identity = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: compiled_release().to_string(),
            commit: compiled_commit().to_string(),
            executable_sha256: "0".repeat(64),
        };
        Self::with_budget_and_identity(budget_bytes, identity)
    }

    fn with_budget_and_identity(budget_bytes: u64, identity: DaemonIdentity) -> Arc<Self> {
        Self::with_budget_policy(budget_bytes, identity, BudgetPolicy::Fixed)
    }

    fn with_budget_policy(
        budget_bytes: u64,
        identity: DaemonIdentity,
        budget_policy: BudgetPolicy,
    ) -> Arc<Self> {
        Arc::new(Self {
            state: Mutex::new(Budget::new(budget_bytes)),
            admit: Condvar::new(),
            admission_identity: AdmissionIdentity::fresh(identity.clone()),
            identity,
            budget_policy,
            #[cfg(unix)]
            active_connections: AtomicUsize::new(0),
            shutting_down: AtomicBool::new(false),
            last_activity: Mutex::new(unix_now()),
            #[cfg(test)]
            refresh_test_gate: Mutex::new(None),
        })
    }

    /// Apply one current effective-memory observation to a production daemon.
    /// A ceiling never rises during a daemon lifetime. Lowering below the live
    /// reservation total is represented as an overcommitted STATUS snapshot
    /// with `free_bytes == 0`; existing work stays accounted and new work is
    /// refused until enough grants leave.
    fn lower_dynamic_budget(&self, observed_bytes: u64) -> bool {
        if self.budget_policy != BudgetPolicy::DynamicMachine {
            return false;
        }
        let mut st = self.lock();
        if observed_bytes >= st.budget_bytes {
            return false;
        }
        st.budget_bytes = observed_bytes;
        drop(st);
        // A waiter whose individual request no longer fits should learn the
        // fail-closed answer promptly instead of sleeping to its old deadline.
        self.admit.notify_all();
        true
    }

    fn refresh_dynamic_budget(&self) -> bool {
        if self.budget_policy != BudgetPolicy::DynamicMachine {
            return false;
        }
        let lowered = self.lower_dynamic_budget(machine_budget_bytes());
        #[cfg(test)]
        let gate = self.refresh_test_gate.lock().unwrap_or_else(|error| error.into_inner()).clone();
        #[cfg(test)]
        if let Some(gate) = gate {
            gate.observed.wait();
            gate.resume.wait();
        }
        lowered
    }

    /// Lock the budget, recovering from a poisoned lock (a panicked handler must
    /// not wedge admission — matches the `memory_jobserver` test-helper pattern).
    fn lock(&self) -> std::sync::MutexGuard<'_, Budget> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn touch_activity(&self) {
        let mut a = self.last_activity.lock().unwrap_or_else(|e| e.into_inner());
        *a = unix_now();
    }

    /// Whether the daemon has been idle (no live reservations, no session
    /// lease and no admission-affecting request) long enough to self-shut-down.
    pub(crate) fn idle_expired(&self) -> bool {
        let st = self.lock();
        if !st.active.is_empty() || st.queue_depth != 0 || st.leases != 0 {
            return false;
        }
        drop(st);
        let last = *self.last_activity.lock().unwrap_or_else(|e| e.into_inner());
        unix_now().saturating_sub(last) >= IDLE_TIMEOUT.as_secs()
    }

    /// Atomically close admission once the idle deadline has elapsed and the
    /// authoritative ledger has no grants, waiters or session leases. Holding
    /// the ledger lock across the flag transition prevents a RESERVE or LEASE
    /// from racing between the empty-state proof and shutdown. The flag is
    /// irreversible for this daemon instance; after it is set, the listener
    /// may durably record CLEAN.
    fn try_begin_idle_shutdown(&self) -> bool {
        let st = self.lock();
        if !st.active.is_empty() || st.queue_depth != 0 || st.leases != 0 {
            return false;
        }
        let last = *self.last_activity.lock().unwrap_or_else(|e| e.into_inner());
        if unix_now().saturating_sub(last) < IDLE_TIMEOUT.as_secs() {
            return false;
        }
        self.shutting_down.store(true, AtomicOrdering::Release);
        true
    }

    /// [`Self::try_begin_idle_shutdown`] without the idle timer: close
    /// admission the moment the authoritative ledger is empty. Used when the
    /// daemon's socket path no longer resolves to its own inode. It can still
    /// serve the clients it already has — their streams survive an unlink —
    /// but no new client can ever reach it, and a client spawns a successor
    /// only once this process is gone, so waiting out the idle interval only
    /// lengthens the outage. The empty-ledger proof is the same one idle
    /// shutdown relies on, so recording CLEAN afterwards is equally sound.
    /// A session lease does not hold it either: a lease exists so the
    /// session's workers find this daemon, and none of them can any more.
    fn try_begin_shutdown_if_unreserved(&self) -> bool {
        let st = self.lock();
        if !st.active.is_empty() || st.queue_depth != 0 {
            return false;
        }
        self.shutting_down.store(true, AtomicOrdering::Release);
        true
    }

    /// Reserve one of the bounded connection-handler slots. The compare/exchange
    /// loop makes the limit exact under concurrent accepts; the RAII permit
    /// returns the slot even if the handler panics or thread creation fails.
    #[cfg(unix)]
    fn try_acquire_connection(self: &Arc<Self>) -> Option<ConnectionPermit> {
        let mut current = self.active_connections.load(AtomicOrdering::Acquire);
        loop {
            if current >= MAX_SERVER_CONNECTIONS {
                return None;
            }
            match self.active_connections.compare_exchange_weak(
                current,
                current + 1,
                AtomicOrdering::AcqRel,
                AtomicOrdering::Acquire,
            ) {
                Ok(_) => return Some(ConnectionPermit { daemon: Arc::clone(self) }),
                Err(observed) => current = observed,
            }
        }
    }

    /// Pair an accepted stream with a handler slot, or send a bounded fail-closed
    /// response and close it when all slots are occupied.
    #[cfg(unix)]
    fn admit_connection(
        self: &Arc<Self>,
        stream: UnixStream,
    ) -> std::io::Result<(ConnectionPermit, UnixStream)> {
        match self.try_acquire_connection() {
            Some(permit) => Ok((permit, stream)),
            None => {
                reject_busy_connection(stream)?;
                Err(std::io::Error::new(
                    std::io::ErrorKind::WouldBlock,
                    "trustd connection limit reached",
                ))
            }
        }
    }

    /// Background maintenance pass: lower the production ceiling from a fresh
    /// host/cgroup observation. Reservation lifetime is exclusively
    /// connection-owned, so this never interprets a client PID across namespace
    /// boundaries and never expires work by age.
    pub(crate) fn refresh_budget_ceiling(&self) {
        self.refresh_dynamic_budget();
    }

    // --- request handlers -------------------------------------------------

    /// RESERVE: deadlock-free blocking admission. Returns the reply line body
    /// (`GRANTED <token>` or `DEGRADED`). The lock is held only while
    /// checking/mutating; `Condvar::wait_timeout` atomically releases the mutex
    /// while a waiter sleeps, so a peer RELEASE can always free bytes.
    fn reserve(&self, bytes: u64, pid: u32, label: String) -> String {
        self.reserve_impl(bytes, pid, label, None).line
    }

    fn reserve_impl(
        &self,
        bytes: u64,
        pid: u32,
        label: String,
        work: Option<AdmissionWork>,
    ) -> ServerReply {
        if self.shutting_down.load(AtomicOrdering::Acquire) {
            return ServerReply::plain("DEGRADED");
        }
        // `RESERVE 0` is inert: hand back sentinel token 0 (RELEASE 0 no-ops),
        // mirroring `acquire(0)`. Not counted in granted_total.
        if bytes == 0 {
            return ServerReply::plain("GRANTED 0");
        }
        let deadline = acquire_deadline();
        let start = Instant::now();
        let mut st = self.lock();
        loop {
            // Re-observe outside the ledger mutex before every grant attempt,
            // including attempts after a condvar wake. This keeps filesystem
            // control-file I/O from blocking RELEASE while ensuring a cgroup
            // reduction during a wait cannot admit against the stale ceiling.
            if self.budget_policy == BudgetPolicy::DynamicMachine {
                drop(st);
                self.refresh_dynamic_budget();
                st = self.lock();
            }
            // This check must follow the dynamic refresh/re-lock. The shutdown
            // owner may have proved an empty ledger and closed admission while
            // this thread had dropped the state mutex for the cgroup read.
            if self.shutting_down.load(AtomicOrdering::Acquire) {
                return ServerReply::plain("DEGRADED");
            }
            // Impossible request (cannot ever fit) or disabled budget ⇒ immediate
            // DEGRADED, never park. Mirrors the file bucket's early-return.
            if st.budget_bytes == 0 || bytes > st.budget_bytes {
                return ServerReply::plain("DEGRADED");
            }
            let next_reserved = st.reserved_bytes.checked_add(bytes);
            let next_sequence = st.granted_total.checked_add(1);
            if work.is_some() {
                if st.evidence_tokens_exhausted
                    || next_sequence.is_none()
                    || st.next_token == 0
                    || st.active.iter().any(|reservation| reservation.token == st.next_token)
                {
                    return ServerReply::plain("ERR evidence-sequence-exhausted");
                }
                if !st.snapshot().has_valid_invariants() {
                    return ServerReply::plain("ERR invalid-evidence-ledger");
                }
                if st.active.iter().any(|reservation| reservation.work.as_ref() == work.as_ref()) {
                    return ServerReply::plain("ERR duplicate-live-work");
                }
            }
            let fits = if work.is_some() {
                next_reserved.is_some_and(|sum| sum <= st.budget_bytes)
            } else {
                st.reserved_bytes.saturating_add(bytes) <= st.budget_bytes
            };
            if fits {
                let token = st.next_token;
                let reply = if let Some(work) = &work {
                    let Some(authority) = &self.admission_identity else {
                        return ServerReply::plain("ERR evidence-unavailable");
                    };
                    let (Some(reserved_after_bytes), Some(grant_sequence)) =
                        (next_reserved, next_sequence)
                    else {
                        return ServerReply::plain("ERR evidence-arithmetic-overflow");
                    };
                    let grant = AdmissionGrant {
                        version: ADMISSION_GRANT_VERSION.to_string(),
                        authority: authority.clone(),
                        token,
                        bytes,
                        budget_at_grant_bytes: st.budget_bytes,
                        reserved_before_bytes: st.reserved_bytes,
                        reserved_after_bytes,
                        grant_sequence,
                        work: work.clone(),
                    };
                    let Ok(json) = serde_json::to_string(&grant) else {
                        return ServerReply::plain("ERR evidence-encoding");
                    };
                    let frame = format!("ADMITTED {json}");
                    if frame.len() > admission::MAX_ADMISSION_REPLY_BYTES {
                        return ServerReply::plain("ERR evidence-too-large");
                    }
                    frame
                } else {
                    format!("GRANTED {token}")
                };
                // Advance, skipping 0 (the inert sentinel) on the wrap.
                st.evidence_tokens_exhausted |= token == u64::MAX;
                st.next_token = st.next_token.wrapping_add(1).max(1);
                st.active.push(ServerReservation {
                    token,
                    pid,
                    bytes,
                    label,
                    granted_at: Instant::now(),
                    work,
                });
                st.reserved_bytes = st.reserved_bytes.saturating_add(bytes);
                st.granted_total = st.granted_total.saturating_add(1);
                return ServerReply { line: reply, token: Some(token) };
            }
            // Does not fit yet: park until a peer releases or the deadline lapses.
            let elapsed = start.elapsed();
            if elapsed >= deadline {
                return ServerReply::plain("DEGRADED");
            }
            let remaining = deadline.saturating_sub(elapsed);
            st.queue_depth = st.queue_depth.saturating_add(1);
            // `wait_timeout` ATOMICALLY releases the mutex while parked — this is
            // the deadlock-free invariant: a releasing peer can always take the
            // lock to free bytes. (In-memory analogue of the file bucket's
            // never-hold-the-flock-while-parked rule.)
            let (guard, timed_out) =
                self.admit.wait_timeout(st, remaining).unwrap_or_else(|e| e.into_inner());
            st = guard;
            st.queue_depth = st.queue_depth.saturating_sub(1);
            if timed_out.timed_out() {
                // The next loop iteration re-checks fit and returns the explicit
                // DEGRADED protocol refusal if the deadline is exhausted. A
                // selected client treats that refusal as an error; it is never a
                // fallback to unreserved work. An early spurious wakeup retries.
                let _ = ();
            }
        }
    }

    /// State-level RELEASE primitive: remove the matching token, credit the
    /// bytes, and wake waiters. It is idempotent for direct/internal callers.
    /// The live connection layer authorizes a nonzero token against that
    /// connection's owned-grant set before this primitive is reachable.
    fn release(&self, token: u64) -> String {
        if token == 0 {
            // Sentinel for an inert (bytes==0) grant: nothing to free.
            return "OK".to_string();
        }
        let mut st = self.lock();
        if let Some(idx) = st.active.iter().position(|r| r.token == token) {
            let bytes = st.active[idx].bytes;
            st.active.remove(idx);
            st.reserved_bytes = st.reserved_bytes.saturating_sub(bytes);
            st.released_total = st.released_total.saturating_add(1);
            drop(st);
            self.admit.notify_all();
        }
        "OK".to_string()
    }

    /// State-level LEASE primitive: hold this daemon for one live verified
    /// session. A session exports this socket to every unit it launches, and a
    /// unit may compile for longer than [`IDLE_TIMEOUT`] before its first
    /// admission; the lease is what keeps the authority the session selected
    /// there when it asks. Minted under the ledger lock, where the idle proof
    /// closes admission, so a lease can never follow a CLEAN shutdown proof:
    /// refused then, its launcher establishes a successor instead. Only the
    /// connection layer calls this, and its guard returns the lease.
    #[cfg(unix)]
    fn acquire_lease(&self) -> bool {
        let mut st = self.lock();
        if self.shutting_down.load(AtomicOrdering::Acquire) {
            return false;
        }
        st.leases = st.leases.saturating_add(1);
        true
    }

    /// Return one session lease. The idle interval restarts here, so a daemon
    /// outlives its last session by [`IDLE_TIMEOUT`], as it outlives its last
    /// grant.
    #[cfg(unix)]
    fn release_lease(&self) {
        self.touch_activity();
        let mut st = self.lock();
        st.leases = st.leases.saturating_sub(1);
    }

    /// STATUS: snapshot and serialize to one line of JSON without mutating
    /// admission state or the idle clock. Reclamation belongs to connection
    /// guards, so a menubar poll cannot free bytes or keep the daemon alive.
    fn status_line(&self) -> String {
        let snap = self.lock().snapshot();
        // Serialization happens OFF the lock. serde_json cannot fail on this
        // owned, finite struct; the fallback keeps the reply one-line on the
        // impossible error path.
        serde_json::to_string(&snap)
            .unwrap_or_else(|_| format!("{{\"version\":\"{STATUS_VERSION}\"}}"))
    }

    fn identity_line(&self) -> String {
        serde_json::to_string(&self.identity)
            .unwrap_or_else(|_| format!("{{\"version\":\"{IDENTITY_VERSION}\"}}"))
    }

    /// Dispatch one request line to its reply line (NO trailing newline; the
    /// caller frames it). The single source of truth for the grammar — both the
    /// daemon binary and the protocol tests route through here.
    pub(crate) fn handle_line(&self, line: &str) -> String {
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.len() > MAX_REQUEST_BYTES {
            return "ERR line-too-long".to_string();
        }
        let verb_end = trimmed.find(' ').unwrap_or(trimmed.len());
        let verb = &trimmed[..verb_end];
        let rest = trimmed[verb_end..].trim_start();

        if verb.eq_ignore_ascii_case("RESERVE") {
            // Operational worker traffic, unlike STATUS/PING, extends the
            // daemon lifetime even when the request is inert or degrades.
            self.touch_activity();
            // `RESERVE <bytes> <pid> <label...>` — label is the rest of the line.
            let mut it = rest.splitn(3, ' ');
            let bytes = match it.next().and_then(|s| s.parse::<u64>().ok()) {
                Some(b) => b,
                None => return "ERR bad-bytes".to_string(),
            };
            let pid = match it.next().and_then(|s| s.parse::<u32>().ok()) {
                Some(p) if p != 0 && p <= i32::MAX as u32 => p,
                None => return "ERR bad-pid".to_string(),
                Some(_) => return "ERR bad-pid".to_string(),
            };
            let mut label = it.next().unwrap_or("").trim().to_string();
            truncate_label(&mut label);
            self.reserve(bytes, pid, label)
        } else if verb.eq_ignore_ascii_case("RESERVE_EVIDENCE") {
            self.touch_activity();
            self.reserve_evidence(rest).line
        } else if verb.eq_ignore_ascii_case("ADMISSION_IDENTITY") {
            if rest.is_empty() {
                self.admission_identity_line()
            } else {
                "ERR bad-args".to_string()
            }
        } else if verb.eq_ignore_ascii_case("RELEASE") {
            self.touch_activity();
            let mut fields = rest.split_whitespace();
            match (fields.next().and_then(|s| s.parse::<u64>().ok()), fields.next()) {
                (Some(token), None) => self.release(token),
                _ => "ERR bad-token".to_string(),
            }
        } else if verb.eq_ignore_ascii_case("STATUS") {
            if rest.is_empty() { self.status_line() } else { "ERR bad-args".to_string() }
        } else if verb.eq_ignore_ascii_case("IDENTITY") {
            if rest.is_empty() { self.identity_line() } else { "ERR bad-args".to_string() }
        } else if verb.eq_ignore_ascii_case("PING") {
            if rest.is_empty() { "PONG".to_string() } else { "ERR bad-args".to_string() }
        } else if verb.eq_ignore_ascii_case("LEASE") {
            // A lease lives exactly as long as the connection holding it, so
            // only `serve_conn` mints one (`ConnectionLease`). A bare request
            // line has no stream whose EOF could end it.
            if rest.is_empty() {
                "ERR connection-owned".to_string()
            } else {
                "ERR bad-args".to_string()
            }
        } else {
            "ERR unknown-verb".to_string()
        }
    }

    /// Serve one connection: read request lines (bounded), reply with one line
    /// each, until the peer closes. Mirrors the original `handle_client` shape
    /// (`BufReader::lines` / `writeln!`).
    #[cfg(unix)]
    pub(crate) fn serve_conn(self: &Arc<Self>, stream: UnixStream) {
        // An admitted proof can legitimately run without another protocol frame
        // for an unbounded time. Clear the initial idle-client timeout after a
        // real grant; timing it out would sever the only RELEASE channel while
        // its live owner still holds the reservation. A session lease is held
        // the same way, by a connection that sends nothing more.
        self.serve_conn_with_read_timeouts(stream, SERVER_INITIAL_READ_TIMEOUT, None);
    }

    #[cfg(all(unix, test))]
    fn serve_conn_with_read_timeout(self: &Arc<Self>, stream: UnixStream, read_timeout: Duration) {
        self.serve_conn_with_read_timeouts(stream, read_timeout, Some(read_timeout));
    }

    #[cfg(unix)]
    fn serve_conn_with_read_timeouts(
        self: &Arc<Self>,
        stream: UnixStream,
        initial_read_timeout: Duration,
        reserved_read_timeout: Option<Duration>,
    ) {
        self.serve_conn_with_reply_hook(
            stream,
            initial_read_timeout,
            reserved_read_timeout,
            |_| {},
        );
    }

    // Production supplies a statically dispatched no-op. Tests can close a peer
    // after grant ownership is installed and before the reply is written,
    // without depending on scheduler or platform socket timing.
    #[cfg(unix)]
    fn serve_conn_with_reply_hook(
        self: &Arc<Self>,
        stream: UnixStream,
        initial_read_timeout: Duration,
        reserved_read_timeout: Option<Duration>,
        mut before_reply: impl FnMut(&ServerReply),
    ) {
        // The production listener is nonblocking. Darwin propagates that mode
        // to accepted descriptors, so normalize each handler stream explicitly;
        // otherwise it serves one buffered command and then mistakes EAGAIN for
        // a terminal protocol error while waiting for the next command.
        if stream.set_nonblocking(false).is_err() {
            return;
        }
        let reader_stream = match stream.try_clone() {
            Ok(s) => s,
            Err(_) => return,
        };
        if reader_stream.set_read_timeout(Some(initial_read_timeout)).is_err() {
            return;
        }
        let mut writer = stream;
        let mut reader = BufReader::new(reader_stream);
        let mut installed_read_timeout = Some(initial_read_timeout);
        // This guard is the grant-lifetime authority. It survives every normal
        // branch and releases all still-owned tokens during panic unwind too.
        // Kernel EOF closes a dead client's stream, so no PID-namespace guess is
        // needed to reclaim its capacity.
        let mut connection_grants = ConnectionGrants::new(Arc::clone(self));
        // The session lease, if this connection takes one, ends on the same
        // EOF, error and unwind paths as its grant.
        let mut connection_lease = ConnectionLease::new(Arc::clone(self));
        loop {
            let Some(line_result) = read_bounded_line(&mut reader) else {
                break;
            };
            let line = match line_result {
                Ok(l) => l,
                Err(_) => break,
            };
            if line.trim().is_empty() {
                continue;
            }
            let requested_release = exact_release_token(&line);
            let requests_nonzero_grant = exact_nonzero_reserve(&line);
            let reply = if exact_lease(&line) {
                ServerReply::plain(&connection_lease.request())
            } else if requests_nonzero_grant && connection_grants.has_live_grant() {
                // The normal client protocol needs exactly one reservation per
                // connection. Bounding that ownership state prevents one
                // authenticated peer from filling the heap/STATUS document with
                // millions of one-byte grants despite the connection cap.
                self.touch_activity();
                ServerReply::plain("ERR outstanding-grant")
            } else if requested_release
                .is_some_and(|token| token != 0 && !connection_grants.contains(token))
            {
                // Tokens are visible in STATUS for diagnostics, so knowledge is
                // not authority. Only the connection that received a live grant
                // may return it; otherwise one client could undercount another
                // worker and cause unsafe over-admission.
                self.touch_activity();
                ServerReply::plain("ERR unowned-token")
            } else if let Some(rest) = admission::evidence_request_body(&line) {
                self.touch_activity();
                self.reserve_evidence(rest)
            } else {
                let line = self.handle_line(&line);
                let token = line
                    .strip_prefix("GRANTED ")
                    .and_then(|token| token.trim().parse::<u64>().ok())
                    .filter(|token| *token != 0);
                ServerReply { line, token }
            };
            if let Some(token) = reply.token {
                // Record before writing the reply: if the peer disappears while
                // the frame is sent, connection cleanup still returns the grant.
                connection_grants.insert(token);
            }
            if reply.line == "OK"
                && let Some(token) = requested_release
            {
                connection_grants.remove(token);
            }
            before_reply(&reply);
            if writeln!(writer, "{}", reply.line).is_err() || writer.flush().is_err() {
                break;
            }
            // Only a live connection-owned grant or session lease may clear the
            // idle timeout: a lease holder sends nothing after LEASED, and its
            // silence is the hold. A successful RELEASE removes a grant's
            // authority above, so reset the ordinary client timeout
            // immediately instead of letting an idle post-release peer retain
            // one handler forever.
            let next_read_timeout =
                if connection_grants.has_live_grant() || connection_lease.is_held() {
                    reserved_read_timeout
                } else {
                    Some(initial_read_timeout)
                };
            if next_read_timeout != installed_read_timeout {
                if reader.get_ref().set_read_timeout(next_read_timeout).is_err() {
                    break;
                }
                installed_read_timeout = next_read_timeout;
            }
        }
    }
}

/// The token stays typed through connection registration. Serialized evidence
/// is not reparsed to decide which capacity belongs to this connection.
struct ServerReply {
    line: String,
    token: Option<u64>,
}

impl ServerReply {
    fn plain(line: &str) -> Self {
        Self { line: line.to_string(), token: None }
    }
}

/// RAII ownership of every live grant minted for one connection. Tokens are
/// returned on EOF, read/write error, or unwind. This is deliberately stronger
/// than `kill(pid, 0)`: client PIDs are not globally meaningful across Linux PID
/// namespaces, while a Unix stream's lifetime is enforced by the kernel.
#[cfg(unix)]
struct ConnectionGrants {
    daemon: Arc<Daemon>,
    token: Option<u64>,
}

#[cfg(unix)]
impl ConnectionGrants {
    fn new(daemon: Arc<Daemon>) -> Self {
        Self { daemon, token: None }
    }

    fn has_live_grant(&self) -> bool {
        self.token.is_some()
    }

    fn contains(&self, token: u64) -> bool {
        self.token == Some(token)
    }

    fn insert(&mut self, token: u64) {
        debug_assert_ne!(token, 0, "the inert sentinel is not a live grant");
        debug_assert!(self.token.is_none(), "one connection may own only one live grant");
        self.token = Some(token);
    }

    fn remove(&mut self, token: u64) {
        if self.token == Some(token) {
            self.token = None;
        }
    }
}

#[cfg(unix)]
impl Drop for ConnectionGrants {
    fn drop(&mut self) {
        if let Some(token) = self.token.take() {
            self.daemon.touch_activity();
            let _ = self.daemon.release(token);
        }
    }
}

/// RAII ownership of the one session lease a connection may hold. Its
/// lifetime is the stream's, for the reason a grant's is: a launcher that
/// dies by any path, SIGKILL included, closes its descriptor, and kernel EOF
/// ends the lease, so no dead session holds a daemon forever and nothing has
/// to judge a PID.
#[cfg(unix)]
struct ConnectionLease {
    daemon: Arc<Daemon>,
    held: bool,
}

#[cfg(unix)]
impl ConnectionLease {
    fn new(daemon: Arc<Daemon>) -> Self {
        Self { daemon, held: false }
    }

    fn is_held(&self) -> bool {
        self.held
    }

    /// Answer one `LEASE` frame. A second one on the same connection is
    /// refused, bounding the ledger as one live grant per connection does.
    fn request(&mut self) -> String {
        if self.held {
            return "ERR outstanding-lease".to_string();
        }
        if !self.daemon.acquire_lease() {
            return "DEGRADED".to_string();
        }
        self.held = true;
        "LEASED".to_string()
    }
}

#[cfg(unix)]
impl Drop for ConnectionLease {
    fn drop(&mut self) {
        if std::mem::take(&mut self.held) {
            self.daemon.release_lease();
        }
    }
}

/// One live connection-handler slot. It owns the daemon Arc so the counter it
/// decrements cannot disappear before the handler exits.
#[cfg(unix)]
struct ConnectionPermit {
    daemon: Arc<Daemon>,
}

#[cfg(unix)]
impl ConnectionPermit {
    fn serve(self, stream: UnixStream) {
        self.daemon.serve_conn(stream);
    }
}

#[cfg(unix)]
impl Drop for ConnectionPermit {
    fn drop(&mut self) {
        let prior = self.daemon.active_connections.try_update(
            AtomicOrdering::AcqRel,
            AtomicOrdering::Acquire,
            |current| current.checked_sub(1),
        );
        debug_assert!(prior.is_ok(), "connection permit counter underflow");
    }
}

/// Once `ERR busy` is delivered, the peer closing is this handshake's SUCCESS
/// case, not a transport failure — there is nobody left to tell. A disconnected
/// Unix socket does not only report that from `read`/`write`: on macOS
/// `setsockopt(SO_RCVTIMEO)` on it fails with `EINVAL` (`InvalidInput`) and
/// `shutdown(2)` with `ENOTCONN` (`NotConnected`). `InvalidInput` is safe to
/// read as "gone" *here* because the only other thing that makes
/// `set_read_timeout` return it is a zero duration, and [`remaining_until`]
/// never yields zero.
///
/// Classifying these as errors made [`Daemon::admit_connection`] answer a
/// connection-limit rejection with a transport kind instead of the `WouldBlock`
/// its contract promises — and the client that triggered it was the
/// *well-behaved* one, which consumed the frame and closed promptly enough to
/// beat the accept thread back to the socket.
#[cfg(unix)]
fn busy_peer_has_left(error: &std::io::Error) -> bool {
    matches!(
        error.kind(),
        std::io::ErrorKind::InvalidInput
            | std::io::ErrorKind::NotConnected
            | std::io::ErrorKind::BrokenPipe
            | std::io::ErrorKind::ConnectionReset
            | std::io::ErrorKind::ConnectionAborted
    )
}

#[cfg(unix)]
fn reject_busy_connection(mut stream: UnixStream) -> std::io::Result<()> {
    // Delivery. A failure before the frame is on the wire IS a transport
    // failure and keeps its own error kind, so a caller can still tell "the
    // saturated daemon could not answer" from "the saturated daemon answered".
    stream.set_write_timeout(Some(OBSERVER_IO_TIMEOUT))?;
    // [`BUSY_REPLY`], framed: a launcher in its lost-race wait reads exactly
    // this line as "at capacity, ask again" ([`ProbeMiss::Busy`]).
    stream.write_all(b"ERR busy\n")?;
    stream.flush()?;

    // Everything below is courtesy: the rejection is delivered, so a peer that
    // has gone away ends the handshake successfully. See [`busy_peer_has_left`].
    if let Err(error) = stream.shutdown(std::net::Shutdown::Write) {
        return if busy_peer_has_left(&error) { Ok(()) } else { Err(error) };
    }

    // Keep the read half alive just long enough for a well-behaved local client
    // to consume the framed rejection and close. On macOS, immediately dropping
    // both halves after shutdown can make a peer that installs its read timeout
    // after connect observe EOF without the queued frame. This bounded handshake
    // has one absolute deadline, runs on the accept thread (never allocates a
    // handler), and discards any input from a saturated client.
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let mut discard = [0u8; 64];
    loop {
        let remaining = match remaining_until(deadline) {
            Ok(value) => value,
            Err(_) => return Ok(()),
        };
        if let Err(error) = stream.set_read_timeout(Some(remaining)) {
            return if busy_peer_has_left(&error) { Ok(()) } else { Err(error) };
        }
        match stream.read(&mut discard) {
            Ok(0) => return Ok(()),
            Ok(_) => continue,
            Err(error)
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::TimedOut | std::io::ErrorKind::WouldBlock
                ) =>
            {
                return Ok(());
            }
            // The rejection frame was already written in full. A peer reset is
            // equivalent to its closing after the response for admission purposes.
            Err(error)
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::ConnectionReset
                        | std::io::ErrorKind::ConnectionAborted
                        | std::io::ErrorKind::BrokenPipe
                ) =>
            {
                return Ok(());
            }
            Err(error) => return Err(error),
        }
    }
}

/// Truncate `label` to [`MAX_LABEL_BYTES`] on a char boundary (never panics).
fn truncate_label(label: &mut String) {
    if label.len() <= MAX_LABEL_BYTES {
        return;
    }
    let mut end = MAX_LABEL_BYTES;
    while end > 0 && !label.is_char_boundary(end) {
        end -= 1;
    }
    label.truncate(end);
}

/// Parse exactly the live protocol's `RELEASE <u64>` shape without mutating
/// daemon state. `serve_conn` uses this before [`Daemon::handle_line`] so a
/// globally visible token cannot become cross-connection release authority.
fn exact_release_token(line: &str) -> Option<u64> {
    let trimmed = line.trim_end_matches(['\r', '\n']);
    if trimmed.len() > MAX_REQUEST_BYTES {
        return None;
    }
    let verb_end = trimmed.find(' ').unwrap_or(trimmed.len());
    let verb = &trimmed[..verb_end];
    if !verb.eq_ignore_ascii_case("RELEASE") {
        return None;
    }
    let mut fields = trimmed[verb_end..].split_whitespace();
    match (fields.next().and_then(|token| token.parse::<u64>().ok()), fields.next()) {
        (Some(token), None) => Some(token),
        _ => None,
    }
}

/// Recognize exactly the argument-free `LEASE` frame, which the connection
/// layer answers itself: the lease belongs to the connection that asked.
fn exact_lease(line: &str) -> bool {
    let trimmed = line.trim_end_matches(['\r', '\n']);
    if trimmed.len() > MAX_REQUEST_BYTES {
        return false;
    }
    let verb_end = trimmed.find(' ').unwrap_or(trimmed.len());
    trimmed[..verb_end].eq_ignore_ascii_case("LEASE") && trimmed[verb_end..].trim_start().is_empty()
}

/// Recognize exactly the subset of `RESERVE` frames that [`Daemon::handle_line`]
/// can turn into a live (nonzero) grant. The connection layer uses this before
/// dispatch to enforce its one-live-grant ownership bound.
fn exact_nonzero_reserve(line: &str) -> bool {
    let trimmed = line.trim_end_matches(['\r', '\n']);
    if trimmed.len() > MAX_REQUEST_BYTES {
        return false;
    }
    let verb_end = trimmed.find(' ').unwrap_or(trimmed.len());
    let verb = &trimmed[..verb_end];
    let rest = trimmed[verb_end..].trim_start();
    if admission::requests_evidence_grant(verb, rest) {
        return true;
    }
    if !verb.eq_ignore_ascii_case("RESERVE") {
        return false;
    }
    let rest = trimmed[verb_end..].trim_start();
    let mut fields = rest.splitn(3, ' ');
    let Some(bytes) = fields.next().and_then(|value| value.parse::<u64>().ok()) else {
        return false;
    };
    let valid_pid = fields
        .next()
        .and_then(|value| value.parse::<u32>().ok())
        .is_some_and(|pid| pid != 0 && pid <= i32::MAX as u32);
    bytes != 0 && valid_pid
}

/// Read one request line, rejecting any line longer than [`MAX_REQUEST_BYTES`]
/// WITHOUT buffering it unbounded (the reader caps the read). A too-long line or
/// read timeout is surfaced as an `Err` so the caller closes the connection.
fn read_bounded_line<R: BufRead>(reader: &mut R) -> Option<Result<String, ()>> {
    let mut buf: Vec<u8> = Vec::with_capacity(64);
    let mut byte = [0u8; 1];
    loop {
        match reader.read(&mut byte) {
            Ok(0) => {
                return if buf.is_empty() {
                    None
                } else {
                    // Every frame is newline-delimited. Accepting a partial
                    // request at EOF would make Rust and Swift clients apply
                    // different wire contracts.
                    Some(Err(()))
                };
            }
            Ok(_) => {
                if byte[0] == b'\n' {
                    return Some(String::from_utf8(buf).map_err(|_| ()));
                }
                if buf.len() >= MAX_REQUEST_BYTES {
                    // Line too long: stop reading and signal an error.
                    return Some(Err(()));
                }
                buf.push(byte[0]);
            }
            Err(_) => return Some(Err(())),
        }
    }
}

// ===========================================================================
// Daemon entry point (called by bin/trustd.rs)
// ===========================================================================

/// Filesystem identity used only while the stable lifetime lock is held, when a
/// new daemon determines whether an old endpoint is stale. Normal shutdown does
/// not unlink socket paths: POSIX has no portable atomic "unlink this inode only"
/// operation, so the next locked owner performs the bounded stale reclamation.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SocketIdentity {
    device: u64,
    inode: u64,
}

#[cfg(unix)]
fn socket_identity(metadata: &std::fs::Metadata) -> SocketIdentity {
    SocketIdentity { device: metadata.dev(), inode: metadata.ino() }
}

/// Canonicalize the socket's parent and enforce the cross-user trust boundary.
/// Cargo target directories may be world-readable, but they must be owned by the
/// effective user and not writable by group/other. A root-owned sticky temporary
/// directory is also safe against cross-user replacement. A symlinked parent is
/// reduced to its canonical target before it is used as the stable lock key.
#[cfg(unix)]
fn canonical_socket_path(path: &Path) -> std::io::Result<PathBuf> {
    let file_name = path.file_name().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("socket path has no filename: {}", path.display()),
        )
    })?;
    let parent =
        path.parent().filter(|value| !value.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let parent = std::fs::canonicalize(parent)?;
    let metadata = std::fs::symlink_metadata(&parent)?;
    let euid = unsafe { libc::geteuid() };
    let mode = metadata.permissions().mode();
    let private_owner_directory = metadata.uid() == euid && mode & 0o022 == 0;
    let root_owned_sticky_directory = metadata.uid() == 0 && mode & (libc::S_ISVTX as u32) != 0;
    if !metadata.file_type().is_dir() || !(private_owner_directory || root_owned_sticky_directory) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!(
                "socket parent must be euid-owned/non-writable or root-owned/sticky: {}",
                parent.display()
            ),
        ));
    }
    validate_authorized_directory_chain(&parent, euid, "trustd socket")?;
    Ok(parent.join(file_name))
}

/// Return the identity at `path`, rejecting anything except an euid-owned,
/// private Unix socket. `symlink_metadata` is intentional: a symlink to a socket
/// is never an endpoint trustd may connect to or reclaim.
#[cfg(unix)]
fn socket_identity_at(path: &Path) -> std::io::Result<Option<SocketIdentity>> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if is_private_owned_socket(&metadata) => Ok(Some(socket_identity(&metadata))),
        Ok(_) => Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!(
                "refusing non-private, foreign-owned, or non-socket endpoint: {}",
                path.display()
            ),
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error),
    }
}

/// An euid-owned, private Unix socket: the only entry trustd treats as an
/// endpoint.
#[cfg(unix)]
fn is_private_owned_socket(metadata: &std::fs::Metadata) -> bool {
    metadata.file_type().is_socket()
        && metadata.uid() == unsafe { libc::geteuid() }
        && metadata.permissions().mode() & 0o077 == 0
}

/// What one refresh tick of [`serve`] learned about its endpoint path.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EndpointCheck {
    /// The path still resolves to this daemon's listener.
    Intact,
    /// The path is gone, or resolves to anything else (another socket, a
    /// non-socket, a foreign-owned or non-private entry): no new client can
    /// reach this daemon.
    Lost,
    /// The path could not be examined (a stat error such as EIO or ENOMEM).
    /// That is no evidence the endpoint is gone; the next tick looks again.
    Unobserved,
}

/// Judge one `symlink_metadata` of `serve`'s endpoint path against the
/// identity its listener was published at. Only a definite answer is loss: a
/// missing path (ENOENT, or ENOTDIR for a component that is no longer a
/// directory) or an entry that is not this listener's private socket.
#[cfg(unix)]
fn endpoint_check(
    observed: std::io::Result<std::fs::Metadata>,
    published: SocketIdentity,
) -> EndpointCheck {
    match observed {
        Ok(metadata)
            if is_private_owned_socket(&metadata) && socket_identity(&metadata) == published =>
        {
            EndpointCheck::Intact
        }
        Ok(_) => EndpointCheck::Lost,
        Err(error)
            if error.kind() == std::io::ErrorKind::NotFound
                || error.raw_os_error() == Some(libc::ENOTDIR) =>
        {
            EndpointCheck::Lost
        }
        Err(_) => EndpointCheck::Unobserved,
    }
}

fn lowercase_sha256(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

#[cfg(unix)]
fn root_owned_immutable_system_parent(parent: &Path) -> std::io::Result<bool> {
    // Root ownership is only an exception for conventional system trees.  A
    // root-owned file in /tmp (or another shared/sticky tree) is not packaged
    // toolchain authority for an unprivileged caller.
    let is_system_path =
        ["/usr", "/bin", "/sbin"].iter().any(|prefix| parent.starts_with(Path::new(*prefix)));
    if !is_system_path {
        return Ok(false);
    }

    let mut cursor = Some(parent);
    while let Some(directory) = cursor {
        let metadata = std::fs::symlink_metadata(directory)?;
        if !metadata.file_type().is_dir()
            || metadata.uid() != 0
            || metadata.permissions().mode() & 0o022 != 0
        {
            return Ok(false);
        }
        cursor = directory.parent();
    }
    Ok(true)
}

#[cfg(unix)]
fn executable_owner_is_trusted(
    effective_uid: u32,
    executable_uid: u32,
    root_owned_immutable_system_path: bool,
) -> bool {
    executable_uid == effective_uid || (executable_uid == 0 && root_owned_immutable_system_path)
}

#[cfg(unix)]
fn executable_metadata_is_trusted(
    metadata: &std::fs::Metadata,
    effective_uid: u32,
    root_owned_immutable_system_path: bool,
) -> bool {
    metadata.file_type().is_file()
        && metadata.permissions().mode() & 0o111 != 0
        && metadata.permissions().mode() & 0o022 == 0
        && executable_owner_is_trusted(
            effective_uid,
            metadata.uid(),
            root_owned_immutable_system_path,
        )
}

#[cfg(unix)]
fn validate_authorized_directory_chain(
    parent: &Path,
    effective_uid: u32,
    authority: &str,
) -> std::io::Result<()> {
    let mut cursor = Some(parent);
    while let Some(directory) = cursor {
        let metadata = std::fs::symlink_metadata(directory)?;
        let mode = metadata.permissions().mode();
        let recognized_owner = metadata.uid() == effective_uid || metadata.uid() == 0;
        let no_cross_user_write = mode & 0o022 == 0;
        let root_owned_sticky = metadata.uid() == 0 && mode & (libc::S_ISVTX as u32) != 0;
        if !metadata.file_type().is_dir()
            || !recognized_owner
            || !(no_cross_user_write || root_owned_sticky)
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                format!(
                    "{authority} ancestor is foreign-owned or cross-user writable: {}",
                    directory.display()
                ),
            ));
        }
        cursor = directory.parent();
    }
    Ok(())
}

#[cfg(unix)]
fn canonical_trusted_executable_path(path: &Path) -> std::io::Result<PathBuf> {
    let file_name = path.file_name().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("trustd executable has no filename: {}", path.display()),
        )
    })?;
    let parent = path.parent().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("trustd executable has no parent: {}", path.display()),
        )
    })?;
    let parent = std::fs::canonicalize(parent)?;
    let euid = unsafe { libc::geteuid() };
    validate_authorized_directory_chain(&parent, euid, "trustd executable")?;
    Ok(parent.join(file_name))
}

#[cfg(unix)]
fn executable_sha256(path: &Path) -> std::io::Result<String> {
    // Resolve the parent once, validate every ancestor to the filesystem root,
    // then use only the resulting canonical pathname for metadata/open/hash.
    // This prevents an untrusted symlinked prefix from being swapped between
    // hashing and the later spawn.
    let path = canonical_trusted_executable_path(path)?;
    let parent = path.parent().expect("canonical executable path retains its parent");
    let euid = unsafe { libc::geteuid() };

    let root_owned_immutable_system_path = root_owned_immutable_system_parent(parent)?;
    let path_metadata = std::fs::symlink_metadata(&path)?;
    if !executable_metadata_is_trusted(&path_metadata, euid, root_owned_immutable_system_path) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!(
                "trustd executable must be same-user (or immutable root-owned system), regular, executable, and have no group/other write bits: {}",
                path.display()
            ),
        ));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
        .open(&path)?;
    let opened_metadata = file.metadata()?;
    if !executable_metadata_is_trusted(&opened_metadata, euid, root_owned_immutable_system_path)
        || socket_identity(&opened_metadata) != socket_identity(&path_metadata)
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("trustd executable changed while opening: {}", path.display()),
        ));
    }

    sha256_file_contents(&mut file)
}

#[cfg(unix)]
fn sha256_file_contents(file: &mut File) -> std::io::Result<String> {
    let mut hasher = Sha256::new();
    let mut chunk = [0u8; 64 * 1024];
    loop {
        let read = file.read(&mut chunk)?;
        if read == 0 {
            break;
        }
        hasher.update(&chunk[..read]);
    }
    Ok(lowercase_sha256(&hasher.finalize()))
}

#[cfg(unix)]
fn daemon_identity_for_executable(path: &Path) -> std::io::Result<DaemonIdentity> {
    Ok(DaemonIdentity {
        version: IDENTITY_VERSION.to_string(),
        protocol: STATUS_VERSION.to_string(),
        release: compiled_release().to_string(),
        commit: compiled_commit().to_string(),
        executable_sha256: executable_sha256(path)?,
    })
}

#[cfg(unix)]
fn runtime_daemon_identity() -> std::io::Result<DaemonIdentity> {
    // Linux exposes an openable reference to the process's actual executable,
    // which remains correct even if Cargo removes/replaces its pathname after
    // exec. macOS does not expose that interface; current_exe is the strongest
    // portable source there and the packaged sibling is immutable to other
    // users by the surrounding toolchain directory permissions.
    #[cfg(target_os = "linux")]
    let executable_sha256 = {
        let mut executable = File::open("/proc/self/exe")?;
        sha256_file_contents(&mut executable)?
    };
    #[cfg(not(target_os = "linux"))]
    let executable_sha256 = executable_sha256(&std::env::current_exe()?)?;

    Ok(DaemonIdentity {
        version: IDENTITY_VERSION.to_string(),
        protocol: STATUS_VERSION.to_string(),
        release: compiled_release().to_string(),
        commit: compiled_commit().to_string(),
        executable_sha256,
    })
}

/// Create and validate the one private runtime namespace for this effective
/// user. A single-component `DirBuilder` is intentional: generic
/// `create_dir_all` could first publish the authority root with ambient 0755
/// permissions. The requested mode is never broader than 0700, and an umask
/// that removes owner bits is repaired before the path is returned.
#[cfg(unix)]
fn private_runtime_root() -> std::io::Result<PathBuf> {
    let euid = unsafe { libc::geteuid() };
    // `/tmp` is intentionally literal rather than `$TMPDIR`: GUI launches,
    // shells, and build services can supply different environment-specific temp
    // directories for the same euid, which would split the authority. Resolve
    // macOS's `/tmp` -> `/private/tmp` alias before deriving the stable path.
    let temp_root = std::fs::canonicalize(Path::new("/tmp"))?;
    validate_authorized_directory_chain(&temp_root, euid, "trustd runtime")?;
    let root = temp_root.join(format!("{LOCK_ROOT_PREFIX}-{euid}"));
    let mut builder = std::fs::DirBuilder::new();
    builder.mode(0o700);
    match builder.create(&root) {
        Ok(()) => {
            if let Err(error) =
                std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700))
            {
                let _ = std::fs::remove_dir(&root);
                return Err(error);
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }

    let metadata = std::fs::symlink_metadata(&root)?;
    if !metadata.file_type().is_dir()
        || metadata.uid() != euid
        || metadata.permissions().mode() & 0o777 != 0o700
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!("trustd runtime root must be an euid-owned 0700 directory: {}", root.display()),
        ));
    }
    validate_authorized_directory_chain(&root, euid, "trustd runtime")?;
    Ok(root)
}

/// Return the normal verified-build memory-authority endpoint. All target
/// directories for one effective user and one trusted `/tmp` backing/mount view
/// rendezvous here, so their simultaneous workers share one visible-memory
/// budget instead of multiplying it per build. A pathname is not authority
/// across split mount namespaces; deployments must keep participants in the
/// same trusted runtime-root mount/identity domain.
#[cfg(unix)]
pub fn host_socket_path() -> std::io::Result<PathBuf> {
    Ok(private_runtime_root()?.join(HOST_SOCKET_NAME))
}

/// The memory-authority endpoint inside an explicitly selected runtime
/// directory ([`RUNTIME_DIR_ENV`]) instead of the per-euid default root.
///
/// The directory is held to the default root's rules — an absolute path to an
/// existing directory owned by this euid with mode 0700, every ancestor owned by
/// this euid or root and not cross-user writable — so relocating the endpoint
/// can never hand it to another user. The path is canonicalized first so a
/// symlinked ancestor (macOS `/tmp`, `/var`) is judged by what it names.
#[cfg(unix)]
pub fn host_socket_path_in(dir: &Path) -> std::io::Result<PathBuf> {
    if !dir.is_absolute() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("trustd runtime directory must be absolute: {}", dir.display()),
        ));
    }
    let euid = unsafe { libc::geteuid() };
    let root = std::fs::canonicalize(dir)?;
    let metadata = std::fs::symlink_metadata(&root)?;
    if !metadata.file_type().is_dir()
        || metadata.uid() != euid
        || metadata.permissions().mode() & 0o777 != 0o700
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!(
                "trustd runtime directory must be an euid-owned 0700 directory: {}",
                root.display()
            ),
        ));
    }
    validate_authorized_directory_chain(&root, euid, "trustd runtime")?;
    Ok(root.join(HOST_SOCKET_NAME))
}

/// Resolve the stable external lock path for a canonical socket path.
#[cfg(unix)]
fn stable_lock_path_for_socket(canonical_socket: &Path) -> std::io::Result<PathBuf> {
    let root = private_runtime_root()?;
    let digest = Sha256::digest(canonical_socket.as_os_str().as_bytes());
    Ok(root.join(format!("{}.lock", lowercase_sha256(&digest))))
}

/// The stable lock file is deliberately never unlinked. Closing the file drops
/// the kernel lock; retaining its inode preserves one rendezvous domain across
/// daemon crashes, idle exits, and deletion/recreation of the Cargo target tree.
/// Its tiny synced record is also a crash epoch: automatic restart is allowed
/// only after the previous owner proved its ledger quiescent and wrote CLEAN.
#[cfg(unix)]
struct StableOwnershipLock {
    file: File,
    path: PathBuf,
}

#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StableEpoch {
    Clean,
    Dirty,
    Invalid,
}

#[cfg(unix)]
const CLEAN_EPOCH_RECORD: &[u8] = b"trustd.epoch.v1 CLEAN\n";
#[cfg(unix)]
const DIRTY_EPOCH_RECORD: &[u8] = b"trustd.epoch.v1 DIRTY\n";
#[cfg(unix)]
const MAX_EPOCH_RECORD_BYTES: u64 = 128;

#[cfg(unix)]
impl StableOwnershipLock {
    fn epoch(&self) -> std::io::Result<StableEpoch> {
        let mut file = self.file.try_clone()?;
        file.seek(SeekFrom::Start(0))?;
        let mut record = Vec::with_capacity(CLEAN_EPOCH_RECORD.len());
        file.take(MAX_EPOCH_RECORD_BYTES + 1).read_to_end(&mut record)?;
        Ok(match record.as_slice() {
            CLEAN_EPOCH_RECORD => StableEpoch::Clean,
            DIRTY_EPOCH_RECORD => StableEpoch::Dirty,
            _ => StableEpoch::Invalid,
        })
    }

    fn write_epoch(&self, record: &[u8]) -> std::io::Result<()> {
        // A crash anywhere after truncation but before the complete sync leaves
        // an invalid record, which is treated exactly like DIRTY. It can never
        // become a false CLEAN transition.
        self.file.set_len(0)?;
        let mut file = self.file.try_clone()?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(record)?;
        file.sync_all()
    }

    fn mark_dirty(&self) -> std::io::Result<()> {
        self.write_epoch(DIRTY_EPOCH_RECORD)
    }

    fn mark_clean(&self) -> std::io::Result<()> {
        self.write_epoch(CLEAN_EPOCH_RECORD)
    }
}

#[cfg(unix)]
fn stable_sentinel_options() -> OpenOptions {
    let mut options = OpenOptions::new();
    options
        .truncate(false)
        .read(true)
        .write(true)
        .mode(0o600)
        .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    options
}

/// Type, owner and mode of an opened sentinel. The link count is deliberately
/// NOT checked here: see [`open_stable_ownership_lock`].
#[cfg(unix)]
fn validate_stable_sentinel(file: &File, path: &Path) -> std::io::Result<()> {
    let metadata = file.metadata()?;
    let euid = unsafe { libc::geteuid() };
    if !metadata.file_type().is_file()
        || metadata.uid() != euid
        || metadata.permissions().mode() & 0o077 != 0
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!(
                "invalid trustd ownership sentinel: {}: it must be a regular file owned by uid {euid} with no group or other permission bits, but it is {} owned by uid {} with mode {:o}. If it is a trustd sentinel, repair it in place (`chmod 600`, as its owner) instead of deleting it: its record is the crash epoch that keeps an unclean daemon from restarting. Anything else at that path is not trustd state: move it aside and retry",
                path.display(),
                if metadata.file_type().is_file() {
                    "a regular file"
                } else {
                    "not a regular file"
                },
                metadata.uid(),
                metadata.permissions().mode() & 0o7777,
            ),
        ));
    }
    Ok(())
}

/// The private pathname under which a creator stages sentinel `name` before
/// linking it into place: `<name>.<pid>-<nonce>-<sequence>.new`, lowercase hex.
#[cfg(unix)]
fn staged_sentinel_name(
    name: &std::ffi::OsStr,
    pid: u32,
    nonce: u128,
    sequence: usize,
) -> std::ffi::OsString {
    let mut staged = name.to_os_string();
    staged.push(format!(".{pid:x}-{nonce:x}-{sequence:x}.new"));
    staged
}

/// The creator pid of `candidate` when it is EXACTLY a staging name of
/// sentinel `name` (the inverse of [`staged_sentinel_name`], canonical hex
/// only); `None` for every other name.
#[cfg(unix)]
fn staged_sentinel_creator(name: &std::ffi::OsStr, candidate: &std::ffi::OsStr) -> Option<u32> {
    fn canonical_hex(field: &[u8]) -> Option<u128> {
        if field.is_empty()
            || field.len() > 32
            || (field.len() > 1 && field[0] == b'0')
            || !field.iter().all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
        {
            return None;
        }
        u128::from_str_radix(std::str::from_utf8(field).ok()?, 16).ok()
    }
    let rest = candidate.as_bytes().strip_prefix(name.as_bytes())?;
    let fields = rest.strip_prefix(b".")?.strip_suffix(b".new")?;
    let mut parts = fields.split(|byte| *byte == b'-');
    let pid = canonical_hex(parts.next()?)?;
    canonical_hex(parts.next()?)?;
    let sequence = canonical_hex(parts.next()?)?;
    if parts.next().is_some() || u64::try_from(sequence).is_err() {
        return None;
    }
    let pid = u32::try_from(pid).ok()?;
    (pid != 0 && libc::pid_t::try_from(pid).is_ok()).then_some(pid)
}

/// Whether `pid` may still be running. Only `ESRCH` proves it gone; a live,
/// zombie, or foreign-credential process (`EPERM`) all count as alive.
#[cfg(unix)]
fn process_may_be_alive(pid: u32) -> bool {
    let Ok(raw) = libc::pid_t::try_from(pid) else {
        return true;
    };
    if raw <= 0 {
        return true;
    }
    if unsafe { libc::kill(raw, 0) } == 0 {
        return true;
    }
    std::io::Error::last_os_error().raw_os_error() != Some(libc::ESRCH)
}

/// Run by the sentinel's LOCK HOLDER only. A published sentinel has exactly one
/// link, except when its creator died (or its unlink failed) between
/// `link(2)` and removing the staging name. That leftover is recognized only
/// when it is a staging name of exactly this sentinel, in the same private
/// runtime root, owned by this euid, naming the SAME inode, and its creator
/// pid is gone. Its content is the creator's CLEAN record (written and synced
/// before the link), and the epoch is classified as usual afterwards, so
/// removing that one name loses nothing. A live creator, or any other extra
/// link, is refused with the steps that clear it.
#[cfg(unix)]
fn reconcile_sentinel_links(file: &File, path: &Path) -> std::io::Result<()> {
    let metadata = file.metadata()?;
    if metadata.nlink() == 1 {
        return Ok(());
    }
    let (parent, name) = match (path.parent(), path.file_name()) {
        (Some(parent), Some(name)) => (parent, name),
        _ => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("ownership sentinel has no parent or file name: {}", path.display()),
            ));
        }
    };
    let euid = unsafe { libc::geteuid() };
    let mut dead_links = Vec::new();
    let mut live_links = Vec::new();
    for entry in std::fs::read_dir(parent)? {
        let entry = entry?;
        let Some(pid) = staged_sentinel_creator(name, &entry.file_name()) else {
            continue;
        };
        let candidate = entry.path();
        let Ok(link) = std::fs::symlink_metadata(&candidate) else {
            continue;
        };
        if !link.file_type().is_file()
            || link.uid() != euid
            || link.dev() != metadata.dev()
            || link.ino() != metadata.ino()
        {
            continue;
        }
        if process_may_be_alive(pid) {
            live_links.push((candidate, pid));
        } else {
            dead_links.push(candidate);
        }
    }

    if metadata.nlink() == 2 && live_links.is_empty() && dead_links.len() == 1 {
        let staged = &dead_links[0];
        std::fs::remove_file(staged).map_err(|error| {
            std::io::Error::new(
                error.kind(),
                format!(
                    "could not remove {}, the staging link a crashed trustd left on ownership sentinel {}: {error}. Delete that staging file by hand (it is only a second name for the sentinel's record; never delete the sentinel itself) and retry",
                    staged.display(),
                    path.display(),
                ),
            )
        })?;
        File::open(parent)?.sync_all()?;
        if file.metadata()?.nlink() == 1 {
            return Ok(());
        }
    }

    let nlink = file.metadata()?.nlink();
    let message = if let Some((staged, pid)) = live_links.first() {
        format!(
            "invalid trustd ownership sentinel: {} has {nlink} links; {} is the staging name of trustd creator pid {pid}, which is still running but did not finish publishing it. Wait for pid {pid} to exit and retry: the staging link is then removed automatically. If pid {pid} is not a trustd or targo process (the pid was reused), delete only {} (never the sentinel, which carries the crash epoch) and retry",
            path.display(),
            staged.display(),
            staged.display(),
        )
    } else {
        format!(
            "invalid trustd ownership sentinel: {} has {nlink} hard links (inode {}), and no staging name in {} from an exited trustd accounts for the extra link, so another pathname aliases the ownership record and writing it could change that file. Find the aliases with `find <mount point> -xdev -inum {}` (`df {}` names the mount point), delete every name except {} (the data stays in the sentinel), and retry. Never delete the sentinel itself: it carries the crash epoch",
            path.display(),
            metadata.ino(),
            parent.display(),
            metadata.ino(),
            parent.display(),
            path.display(),
        )
    };
    Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, message))
}

/// Run by the sentinel's LOCK HOLDER only: remove this sentinel's staging files
/// whose creator died before publishing them (single-linked, euid-owned,
/// dead pid). A live creator's staging file is never touched, and a reused pid
/// cannot collide with the old name because `create_new` refuses it. Removal is
/// best-effort housekeeping: a failure leaves an inert file and never affects
/// ownership.
#[cfg(unix)]
fn remove_orphaned_sentinel_stages(file: &File, path: &Path) {
    let (Some(parent), Some(name), Ok(sentinel)) =
        (path.parent(), path.file_name(), file.metadata())
    else {
        return;
    };
    let Ok(entries) = std::fs::read_dir(parent) else {
        return;
    };
    let euid = unsafe { libc::geteuid() };
    let mut removed = false;
    for entry in entries.flatten() {
        let Some(pid) = staged_sentinel_creator(name, &entry.file_name()) else {
            continue;
        };
        let candidate = entry.path();
        let Ok(stage) = std::fs::symlink_metadata(&candidate) else {
            continue;
        };
        if !stage.file_type().is_file()
            || stage.uid() != euid
            || stage.nlink() != 1
            || (stage.dev() == sentinel.dev() && stage.ino() == sentinel.ino())
            || process_may_be_alive(pid)
        {
            continue;
        }
        removed |= std::fs::remove_file(&candidate).is_ok();
    }
    if removed {
        if let Ok(directory) = File::open(parent) {
            let _ = directory.sync_all();
        }
    }
}

#[cfg(unix)]
fn try_lock_stable_sentinel(file: &File, canonical_socket: &Path) -> std::io::Result<()> {
    let result = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
    if result == 0 {
        return Ok(());
    }
    let error = std::io::Error::last_os_error();
    let raw = error.raw_os_error();
    if raw == Some(libc::EWOULDBLOCK) || raw == Some(libc::EAGAIN) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::AddrInUse,
            format!("{OWNED_ELSEWHERE} {}", canonical_socket.display()),
        ));
    }
    Err(error)
}

/// Removes a staged sentinel pathname unless publication completed.
#[cfg(unix)]
struct StagedStableSentinel {
    path: Option<PathBuf>,
}

#[cfg(unix)]
impl Drop for StagedStableSentinel {
    fn drop(&mut self) {
        if let Some(path) = self.path.take() {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// Create the sentinel at `path` ALREADY LOCKED and ALREADY CLEAN, or return
/// `None` when another process published it first.
///
/// The record is written and synced on a private staging inode that this
/// process has flocked, and only then linked into place (`link(2)` refuses an
/// existing target atomically). No other process can therefore ever open an
/// uninitialized sentinel, and any process that opens the published one while
/// this creator lives observes its lock. The previous create-then-lock order
/// exposed an empty record to a peer that won the flock race; the creator then
/// lost its own flock and returned `AddrInUse` while the peer refused the
/// "invalid" epoch — leaving the endpoint with no owner at all.
#[cfg(unix)]
fn create_locked_clean_sentinel(
    path: &Path,
    canonical_socket: &Path,
) -> std::io::Result<Option<StableOwnershipLock>> {
    static NEXT_SENTINEL_STAGE: AtomicUsize = AtomicUsize::new(0);
    let parent = path.parent().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("ownership sentinel has no parent: {}", path.display()),
        )
    })?;
    let name = path.file_name().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("ownership sentinel has no file name: {}", path.display()),
        )
    })?;
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    let (file, staged) = {
        let mut attempt = 0;
        loop {
            let sequence = NEXT_SENTINEL_STAGE.fetch_add(1, AtomicOrdering::Relaxed);
            let staged =
                parent.join(staged_sentinel_name(name, std::process::id(), nonce, sequence));
            match stable_sentinel_options().create_new(true).open(&staged) {
                Ok(file) => break (file, StagedStableSentinel { path: Some(staged) }),
                Err(error)
                    if error.kind() == std::io::ErrorKind::AlreadyExists && attempt < 128 =>
                {
                    attempt += 1;
                }
                Err(error) => return Err(error),
            }
        }
    };
    let staged_path = staged.path.clone().expect("staged sentinel path is present");
    validate_stable_sentinel(&file, &staged_path)?;
    // A fresh, unpublished private inode: nobody else can hold its lock.
    try_lock_stable_sentinel(&file, canonical_socket)?;
    let mut ownership = StableOwnershipLock { file, path: staged_path.clone() };
    ownership.mark_clean()?;

    match std::fs::hard_link(&staged_path, path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => return Ok(None),
        Err(error) => return Err(error),
    }
    // Still holding the lock, drop the staging name so the published inode has
    // exactly one link. A failure here (or a crash before it) leaves link count
    // 2: fail closed rather than hand out ownership of it. The next lock holder
    // removes the staging link once this process has exited
    // (`reconcile_sentinel_links`).
    let mut staged = staged;
    staged.path = None;
    std::fs::remove_file(&staged_path)?;
    // Sync the directory so the rendezvous survives a system crash.
    File::open(parent)?.sync_all()?;
    ownership.path = path.to_path_buf();
    Ok(Some(ownership))
}

#[cfg(unix)]
fn open_stable_ownership_lock(
    canonical_socket: &Path,
) -> std::io::Result<(StableOwnershipLock, StableEpoch)> {
    let path = stable_lock_path_for_socket(canonical_socket)?;
    if let Some(ownership) = create_locked_clean_sentinel(&path, canonical_socket)? {
        remove_orphaned_sentinel_stages(&ownership.file, &ownership.path);
        let epoch = ownership.epoch()?;
        return Ok((ownership, epoch));
    }

    let file = stable_sentinel_options().open(&path)?;
    validate_stable_sentinel(&file, &path)?;
    try_lock_stable_sentinel(&file, canonical_socket)?;
    // The link count is checked only once the lock is held. A live creator keeps
    // its lock across the instant between publishing the sentinel and removing
    // its staging name (link count 2), so a contender in that instant reports
    // `AddrInUse` above; a LOCK HOLDER can never observe that instant. An extra
    // link it does observe is either a dead creator's staging name (removed
    // here) or foreign (refused).
    reconcile_sentinel_links(&file, &path)?;
    remove_orphaned_sentinel_stages(&file, &path);
    let ownership = StableOwnershipLock { file, path };
    let epoch = ownership.epoch()?;
    Ok((ownership, epoch))
}

#[cfg(unix)]
fn try_stable_ownership_lock(canonical_socket: &Path) -> std::io::Result<StableOwnershipLock> {
    // Sentinels are published only already-CLEAN (see
    // `create_locked_clean_sentinel`), so any non-CLEAN record a lock holder
    // reads was left by a prior owner: DIRTY, or torn by a crash mid-write.
    // Both fail closed immediately; no initialization grace is needed.
    let (ownership, epoch) = open_stable_ownership_lock(canonical_socket)?;
    if epoch == StableEpoch::Clean {
        return Ok(ownership);
    }
    drop(ownership);
    Err(std::io::Error::new(
        std::io::ErrorKind::Other,
        format!(
            "trustd crash epoch is not CLEAN for {}; automatic restart is refused because a prior solver may still hold memory. Establish every solver from the prior daemon is gone, then invoke `/absolute/path/to/selected/sysroot/bin/trustd --recover-after-crash --confirm-no-solvers --socket {}`: derive that absolute trustd as the same-sysroot sibling of the selected, validated Targo, never from ambient PATH. The path relation does not itself prove packaged byte or execution identity; the confirmation is an operator attestation, not a process check, so reboot first if uncertain",
            canonical_socket.display(),
            canonical_socket.display(),
        ),
    ))
}

/// A bound endpoint plus the external advisory lock proving this process is its
/// sole daemon owner. Dropping it closes the listener and releases the kernel
/// lock, but intentionally leaves both socket and lock sentinel for the next
/// locked owner to classify/reclaim.
#[cfg(unix)]
struct OwnedSocket {
    listener: UnixListener,
    /// The inode this listener was published at. `serve` re-checks the path
    /// against it every refresh tick: a path that no longer resolves here can
    /// never deliver a new client, so the daemon drains and exits CLEAN.
    identity: SocketIdentity,
    ownership_lock: StableOwnershipLock,
}

#[cfg(unix)]
impl OwnedSocket {
    fn mark_dirty(&self) -> std::io::Result<()> {
        self.ownership_lock.mark_dirty()
    }

    fn mark_clean(&self) -> std::io::Result<()> {
        self.ownership_lock.mark_clean()
    }
}

#[cfg(unix)]
fn stale_connect_error(error: &std::io::Error) -> bool {
    error.raw_os_error() == Some(libc::ECONNREFUSED)
}

/// Deadline-bounded AF_UNIX connect. `UnixStream::connect` has no timeout API,
/// so use a nonblocking descriptor and poll completion on both macOS and Linux.
///
/// The descriptor is close-on-exec. On Linux it is born so (`SOCK_CLOEXEC`),
/// atomically. Darwin has no `SOCK_CLOEXEC`, so there `fcntl` sets the flag
/// just after `socket(2)`, and a child another thread of this process spawns
/// between the two calls inherits the connection for that child's whole life;
/// for a [`DaemonLease`] that copy holds the daemon until the child exits.
#[cfg(unix)]
fn connect_unix_until(path: &Path, deadline: Instant) -> std::io::Result<UnixStream> {
    #[cfg(target_os = "linux")]
    let socket_type = libc::SOCK_STREAM | libc::SOCK_CLOEXEC;
    #[cfg(not(target_os = "linux"))]
    let socket_type = libc::SOCK_STREAM;
    let raw_fd = unsafe { libc::socket(libc::AF_UNIX, socket_type, 0) };
    if raw_fd < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let owned = unsafe { OwnedFd::from_raw_fd(raw_fd) };

    #[cfg(not(target_os = "linux"))]
    {
        let descriptor_flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFD) };
        if descriptor_flags < 0
            || unsafe {
                libc::fcntl(owned.as_raw_fd(), libc::F_SETFD, descriptor_flags | libc::FD_CLOEXEC)
            } < 0
        {
            return Err(std::io::Error::last_os_error());
        }
    }
    let status_flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFL) };
    if status_flags < 0
        || unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_SETFL, status_flags | libc::O_NONBLOCK) }
            < 0
    {
        return Err(std::io::Error::last_os_error());
    }

    let path_bytes = path.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if path_bytes.is_empty()
        || path_bytes.contains(&0)
        || path_bytes.len() >= address.sun_path.len()
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("invalid or overlong Unix socket path: {}", path.display()),
        ));
    }
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    // Match std's Unix socket address length: only the family, pathname bytes,
    // and terminating NUL are part of the address. Darwin uses this supplied
    // length when interpreting pathname sockets; passing the full struct merely
    // happened to work for the ASCII cases and diverged from the bind address.
    let address_len = std::mem::offset_of!(libc::sockaddr_un, sun_path)
        .checked_add(path_bytes.len())
        .and_then(|length| length.checked_add(1))
        .ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidInput, "Unix socket address overflow")
        })?;
    #[cfg(any(
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "dragonfly",
        target_os = "netbsd",
        target_os = "openbsd"
    ))]
    {
        address.sun_len = address_len as u8;
    }
    unsafe {
        std::ptr::copy_nonoverlapping(
            path_bytes.as_ptr(),
            address.sun_path.as_mut_ptr().cast::<u8>(),
            path_bytes.len(),
        );
    }

    let connected = unsafe {
        libc::connect(
            owned.as_raw_fd(),
            std::ptr::addr_of!(address).cast::<libc::sockaddr>(),
            address_len as libc::socklen_t,
        )
    };
    if connected != 0 {
        let error = std::io::Error::last_os_error();
        if !matches!(error.raw_os_error(), Some(libc::EINPROGRESS) | Some(libc::EAGAIN)) {
            return Err(error);
        }

        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!("timed out connecting to {}", path.display()),
                ));
            }
            let timeout_ms = remaining.as_millis().max(1).min(i32::MAX as u128) as i32;
            let mut poll_fd =
                libc::pollfd { fd: owned.as_raw_fd(), events: libc::POLLOUT, revents: 0 };
            let polled = unsafe { libc::poll(&mut poll_fd, 1, timeout_ms) };
            if polled < 0 {
                let error = std::io::Error::last_os_error();
                if error.kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if polled == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!("timed out connecting to {}", path.display()),
                ));
            }

            let mut socket_error: libc::c_int = 0;
            let mut socket_error_len = std::mem::size_of_val(&socket_error) as libc::socklen_t;
            if unsafe {
                libc::getsockopt(
                    owned.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_ERROR,
                    std::ptr::addr_of_mut!(socket_error).cast::<libc::c_void>(),
                    &mut socket_error_len,
                )
            } != 0
            {
                return Err(std::io::Error::last_os_error());
            }
            if socket_error != 0 {
                return Err(std::io::Error::from_raw_os_error(socket_error));
            }
            break;
        }
    }

    if unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_SETFL, status_flags & !libc::O_NONBLOCK) }
        < 0
    {
        return Err(std::io::Error::last_os_error());
    }
    Ok(UnixStream::from(owned))
}

#[cfg(target_os = "macos")]
fn connected_peer_pid(stream: &UnixStream) -> std::io::Result<u32> {
    let mut pid: libc::pid_t = 0;
    let mut len = std::mem::size_of_val(&pid) as libc::socklen_t;
    // SAFETY: pid is writable for exactly len bytes and stream owns a live fd.
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_LOCAL,
            libc::LOCAL_PEERPID,
            std::ptr::addr_of_mut!(pid).cast(),
            &mut len,
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error());
    }
    if len as usize != std::mem::size_of_val(&pid) || pid <= 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "connected Unix peer returned no valid LOCAL_PEERPID",
        ));
    }
    Ok(pid as u32)
}

#[cfg(target_os = "linux")]
fn connected_peer_pid(stream: &UnixStream) -> std::io::Result<u32> {
    let mut credentials: libc::ucred = unsafe { std::mem::zeroed() };
    let mut len = std::mem::size_of_val(&credentials) as libc::socklen_t;
    // SAFETY: credentials is writable for exactly len bytes and stream owns a live fd.
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            std::ptr::addr_of_mut!(credentials).cast(),
            &mut len,
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error());
    }
    if len as usize != std::mem::size_of_val(&credentials) || credentials.pid <= 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "connected Unix peer returned no valid SO_PEERCRED PID",
        ));
    }
    Ok(credentials.pid as u32)
}

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
fn connected_peer_pid(_stream: &UnixStream) -> std::io::Result<u32> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "trustd peer-PID binding is implemented only on macOS and Linux",
    ))
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn require_live_unreaped_child(pid: u32) -> std::io::Result<()> {
    let pid = i32::try_from(pid).ok().filter(|pid| *pid > 0).ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, "invalid spawned child PID")
    })?;
    let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
    // SAFETY: waitid writes info, and WNOWAIT observes without releasing the child PID.
    if unsafe {
        libc::waitid(
            libc::P_PID,
            pid as libc::id_t,
            info.as_mut_ptr(),
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error());
    }
    if unsafe { info.assume_init().si_pid() } != 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::BrokenPipe,
            "spawned trustd child has exited",
        ));
    }
    Ok(())
}

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
fn require_live_unreaped_child(_pid: u32) -> std::io::Result<()> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "trustd child-liveness binding is implemented only on macOS and Linux",
    ))
}

#[cfg(unix)]
fn connect_trusted_until_with_pid(
    path: &Path,
    deadline: Instant,
    expected_peer_pid: Option<u32>,
) -> std::io::Result<UnixStream> {
    if let Some(expected) = expected_peer_pid {
        require_live_unreaped_child(expected)?;
    }
    let canonical = canonical_socket_path(path)?;
    let before = socket_identity_at(&canonical)?.ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("trustd socket is absent: {}", canonical.display()),
        )
    })?;
    let stream = connect_unix_until(&canonical, deadline)?;
    if socket_identity_at(&canonical)? != Some(before) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::ConnectionAborted,
            format!("trustd socket changed while connecting: {}", canonical.display()),
        ));
    }
    if let Some(expected) = expected_peer_pid {
        let actual = connected_peer_pid(&stream)?;
        if actual != expected {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                format!(
                    "trustd socket peer PID {actual} differs from spawned child PID {expected}"
                ),
            ));
        }
        require_live_unreaped_child(expected)?;
    }
    Ok(stream)
}

/// A socket bound below a private staging directory but not yet published at
/// its rendezvous path. Drop removes only the unpublished staging artifacts.
#[cfg(unix)]
struct PrivateSocketStage {
    listener: Option<UnixListener>,
    directory: PathBuf,
    socket: PathBuf,
    identity: SocketIdentity,
}

#[cfg(unix)]
impl Drop for PrivateSocketStage {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.socket);
        let _ = std::fs::remove_dir(&self.directory);
    }
}

#[cfg(unix)]
fn remove_socket_with_identity(path: &Path, identity: SocketIdentity) {
    if std::fs::symlink_metadata(path).is_ok_and(|metadata| {
        metadata.file_type().is_socket() && socket_identity(&metadata) == identity
    }) {
        let _ = std::fs::remove_file(path);
    }
}

#[cfg(unix)]
impl PrivateSocketStage {
    fn publish(mut self, target: &Path) -> std::io::Result<UnixListener> {
        match std::fs::symlink_metadata(target) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::AlreadyExists,
                    format!(
                        "refusing to replace socket path while publishing: {}",
                        target.display()
                    ),
                ));
            }
            Err(error) => return Err(error),
        }
        std::fs::rename(&self.socket, target)?;
        let metadata = match std::fs::symlink_metadata(target) {
            Ok(metadata) => metadata,
            Err(error) => {
                remove_socket_with_identity(target, self.identity);
                return Err(error);
            }
        };
        if !metadata.file_type().is_socket()
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.permissions().mode() & 0o077 != 0
            || socket_identity(&metadata) != self.identity
        {
            // Remove only the inode this stage published; preserve any pathname
            // replacement installed after the rename.
            remove_socket_with_identity(target, self.identity);
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                format!("published trustd socket lost its private identity: {}", target.display()),
            ));
        }
        Ok(self.listener.take().expect("staged listener is present until publication"))
    }
}

/// Bind inside an atomically-private child directory, chmod the socket while it
/// is unreachable to other users, then let [`PrivateSocketStage::publish`]
/// rename it into place. Unlike a temporary `umask`, this never mutates
/// process-global state in a multithreaded compiler/test process.
#[cfg(unix)]
fn stage_private_socket(parent: &Path) -> std::io::Result<PrivateSocketStage> {
    static NEXT_STAGE: AtomicUsize = AtomicUsize::new(0);
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    let mut directory = None;
    for _ in 0..128 {
        let sequence = NEXT_STAGE.fetch_add(1, AtomicOrdering::Relaxed);
        let candidate = parent.join(format!(".td-{:x}-{nonce:x}-{sequence:x}", std::process::id()));
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        match builder.create(&candidate) {
            Ok(()) => {
                // A restrictive ambient umask may remove owner execute. Restore
                // owner access; requested 0700 ensured no cross-user bit was ever
                // present during creation.
                if let Err(error) =
                    std::fs::set_permissions(&candidate, std::fs::Permissions::from_mode(0o700))
                {
                    let _ = std::fs::remove_dir(&candidate);
                    return Err(error);
                }
                directory = Some(candidate);
                break;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    let directory = directory.ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            format!(
                "could not allocate private socket staging directory below {}",
                parent.display()
            ),
        )
    })?;
    let metadata = match std::fs::symlink_metadata(&directory) {
        Ok(metadata) => metadata,
        Err(error) => {
            let _ = std::fs::remove_dir(&directory);
            return Err(error);
        }
    };
    if !metadata.file_type().is_dir()
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o077 != 0
    {
        let _ = std::fs::remove_dir(&directory);
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!("invalid private socket staging directory: {}", directory.display()),
        ));
    }

    let socket = directory.join("s");
    let listener = match UnixListener::bind(&socket) {
        Ok(listener) => listener,
        Err(error) => {
            let _ = std::fs::remove_dir(&directory);
            return Err(error);
        }
    };
    if let Err(error) = std::fs::set_permissions(&socket, std::fs::Permissions::from_mode(0o600)) {
        drop(listener);
        let _ = std::fs::remove_file(&socket);
        let _ = std::fs::remove_dir(&directory);
        return Err(error);
    }
    let socket_metadata = match std::fs::symlink_metadata(&socket) {
        Ok(metadata) => metadata,
        Err(error) => {
            drop(listener);
            let _ = std::fs::remove_file(&socket);
            let _ = std::fs::remove_dir(&directory);
            return Err(error);
        }
    };
    if !socket_metadata.file_type().is_socket()
        || socket_metadata.uid() != unsafe { libc::geteuid() }
        || socket_metadata.permissions().mode() & 0o077 != 0
    {
        drop(listener);
        let _ = std::fs::remove_file(&socket);
        let _ = std::fs::remove_dir(&directory);
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!("staged trustd socket is not private: {}", socket.display()),
        ));
    }
    let identity = socket_identity(&socket_metadata);
    Ok(PrivateSocketStage { listener: Some(listener), directory, socket, identity })
}

#[cfg(unix)]
fn bind_private_socket(path: &Path) -> std::io::Result<UnixListener> {
    let parent = path.parent().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("socket path has no parent: {}", path.display()),
        )
    })?;
    stage_private_socket(parent)?.publish(path)
}

/// Acquire lifetime ownership and bind a private socket. Under the ownership
/// lock, an unreachable old private socket can be reclaimed. A live socket,
/// foreign-owned endpoint, non-private endpoint, regular file, directory, or
/// symlink is always refused. Same-euid path mutation is outside the threat
/// boundary; cross-user mutation is excluded by the validated parent directory.
#[cfg(unix)]
fn bind_owned_socket(sock: &Path) -> std::io::Result<OwnedSocket> {
    let canonical = canonical_socket_path(sock)?;
    let ownership_lock = try_stable_ownership_lock(&canonical)?;

    if let Some(stale_identity) = socket_identity_at(&canonical)? {
        // A successful or ambiguous connection attempt means the endpoint may
        // still be live. Only the kernel's explicit connection-refused result is
        // classified as stale and reclaimed while the stable lock is held.
        match connect_unix_until(
            &canonical,
            Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now),
        ) {
            Ok(stream) => {
                drop(stream);
                return Err(std::io::Error::new(
                    std::io::ErrorKind::AddrInUse,
                    format!("a live listener already owns {}", canonical.display()),
                ));
            }
            Err(error) if stale_connect_error(&error) => {}
            Err(error) => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::AddrInUse,
                    format!(
                        "refusing to reclaim possibly-live socket {}: {error}",
                        canonical.display()
                    ),
                ));
            }
        }
        if socket_identity_at(&canonical)? != Some(stale_identity) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                format!("socket path changed while reclaiming {}", canonical.display()),
            ));
        }
        std::fs::remove_file(&canonical)?;
    }

    let listener = bind_private_socket(&canonical)?;
    let identity = socket_identity_at(&canonical)?.ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("bound socket path disappeared: {}", canonical.display()),
        )
    })?;

    if socket_identity_at(&canonical)? != Some(identity) {
        drop(listener);
        return Err(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            format!("socket path changed while binding {}", canonical.display()),
        ));
    }

    Ok(OwnedSocket { listener, identity, ownership_lock })
}

/// Bind and complete every fallible pre-admission listener initialization
/// before arming the durable crash epoch. The listener can queue connections
/// while `initialize` runs, but no request is accepted or admitted until after
/// DIRTY is durable. Consequently an `initialize` failure leaves a provably
/// empty CLEAN epoch that may restart automatically. Failure while persisting
/// DIRTY itself may leave an invalid epoch and deliberately remains fail-closed.
#[cfg(unix)]
fn prepare_owned_socket<F>(sock: &Path, initialize: F) -> std::io::Result<OwnedSocket>
where
    F: FnOnce(&UnixListener) -> std::io::Result<()>,
{
    let owned = bind_owned_socket(sock)?;
    initialize(&owned.listener)?;
    owned.mark_dirty()?;
    Ok(owned)
}

/// Explicit operator recovery for an unclean daemon epoch. The CLI requires a
/// separate `--confirm-no-solvers` assertion before calling this: the kernel
/// lock proves the old daemon is gone, but only the operator can establish that
/// every solver admitted by it has also quiesced. A reachable endpoint is always
/// refused, and this function never removes the stale socket.
#[cfg(unix)]
pub fn recover_dirty_epoch_after_quiescence(sock: &Path) -> std::io::Result<bool> {
    let canonical = canonical_socket_path(sock)?;
    let (ownership, epoch) = open_stable_ownership_lock(&canonical)?;

    if let Some(identity) = socket_identity_at(&canonical)? {
        match connect_unix_until(
            &canonical,
            Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now),
        ) {
            Ok(stream) => {
                drop(stream);
                return Err(std::io::Error::new(
                    std::io::ErrorKind::AddrInUse,
                    format!("a live listener still owns {}", canonical.display()),
                ));
            }
            Err(error) if stale_connect_error(&error) => {}
            Err(error) => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::AddrInUse,
                    format!(
                        "cannot prove the endpoint stale during crash recovery {}: {error}",
                        canonical.display()
                    ),
                ));
            }
        }
        if socket_identity_at(&canonical)? != Some(identity) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                format!("socket path changed during crash recovery: {}", canonical.display()),
            ));
        }
    }

    if epoch == StableEpoch::Clean {
        return Ok(false);
    }
    ownership.mark_clean()?;
    Ok(true)
}

/// Write one line to trustd's stderr WITHOUT panicking on a failed write.
///
/// A daemon started by [`ensure_daemon`] writes stderr into a pipe read by the
/// launcher (`capture_spawned_stderr`), and that launcher (a `targo` run, a
/// CI step, a `timeout`-wrapped probe) routinely exits long before the
/// daemon's idle shutdown. From then on the pipe has no reader. Rust ignores
/// SIGPIPE, so the write fails with EPIPE, and `eprintln!` PANICS on a failed
/// write; on the accept thread that panic is an unclean exit that leaves the
/// crash epoch DIRTY and refuses automatic restart for every verified build on
/// the host until an operator recovers it. Every write trustd can make after it
/// has published its endpoint goes through here: a lost diagnostic line is
/// always cheaper than a lost memory authority.
#[doc(hidden)]
pub fn daemon_diagnostic(message: std::fmt::Arguments<'_>) {
    let _ = writeln!(std::io::stderr(), "{message}");
}

/// Bind the daemon to `sock` and serve until a proven-quiescent idle shutdown.
/// A stable per-socket lock and durable DIRTY epoch are held for the complete
/// lifetime. Only the admission-closed, empty-ledger shutdown path writes CLEAN;
/// errors, aborts, OOM, and SIGKILL therefore make automatic restart fail closed.
/// Normal shutdown never unlinks the endpoint; the next locked owner reclaims it.
#[cfg(unix)]
pub fn serve(sock: &Path) -> std::io::Result<()> {
    let identity = runtime_daemon_identity()?;
    let daemon = Daemon::new(identity);
    let owned = prepare_owned_socket(sock, |listener| listener.set_nonblocking(true))?;
    let canonical = canonical_socket_path(sock)?;
    let mut endpoint_lost_reported = false;

    // The accept loop owns the clean transition. Keeping refresh, the idle proof,
    // admission closure, and epoch sync in this thread avoids process::exit from
    // a maintenance thread bypassing the durable shutdown protocol.
    let mut next_refresh =
        Instant::now().checked_add(BUDGET_REFRESH_INTERVAL).unwrap_or_else(Instant::now);
    loop {
        let now = Instant::now();
        if now >= next_refresh {
            daemon.refresh_budget_ceiling();
            next_refresh = now.checked_add(BUDGET_REFRESH_INTERVAL).unwrap_or_else(Instant::now);
            // Self-defence: the endpoint path must still resolve to THIS
            // listener's inode. If anything unlinked or replaced it — a test
            // stub, an operator, a temp cleaner — no new client can reach this
            // daemon, every admission on the host fails "trustd socket is
            // absent", and nothing restarts it: a client only spawns a
            // successor after this process is gone. On 2026-09-19 a test stub
            // did exactly that to a live gate and 282,786 obligations failed
            // admission in eight seconds. Drain the clients already connected,
            // then exit CLEAN so the next client re-establishes the authority.
            // Never re-bind here: the path may now belong to a live successor,
            // and POSIX has no atomic "unlink only my inode". A stat that
            // failed (EIO, ENOMEM) is not loss: draining on it would end a
            // daemon its sessions still lease between two admissions, and
            // every later unit would meet ECONNREFUSED. That tick only checks
            // idleness, which is sound whatever the endpoint state.
            match endpoint_check(std::fs::symlink_metadata(&canonical), owned.identity) {
                EndpointCheck::Lost => {
                    if !endpoint_lost_reported {
                        // Post-readiness write: never `eprintln!` (see
                        // `daemon_diagnostic`). A panic here would skip the
                        // CLEAN transition below and strand the host epoch
                        // DIRTY.
                        daemon_diagnostic(format_args!(
                            "trustd: endpoint {} no longer resolves to this daemon; \
                             refusing new clients, draining, then exiting",
                            canonical.display()
                        ));
                        endpoint_lost_reported = true;
                    }
                    if daemon.try_begin_shutdown_if_unreserved() {
                        owned.mark_clean()?;
                        return Ok(());
                    }
                }
                EndpointCheck::Intact | EndpointCheck::Unobserved => {
                    if daemon.try_begin_idle_shutdown() {
                        owned.mark_clean()?;
                        return Ok(());
                    }
                }
            }
        }

        match owned.listener.accept() {
            Ok((stream, _)) => {
                let daemon = Arc::clone(&daemon);
                let Ok((permit, stream)) = daemon.admit_connection(stream) else {
                    continue;
                };
                let _ = thread::Builder::new()
                    .name("trustd-connection".to_string())
                    .spawn(move || permit.serve(stream));
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                let until_refresh = next_refresh.saturating_duration_since(Instant::now());
                thread::sleep(until_refresh.min(Duration::from_millis(20)));
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
}

// ===========================================================================
// Client API (the ONE seam trustc + the in-process backend call)
// ===========================================================================

/// A held reservation. Releases on `Drop` via the same path it was acquired:
/// DAEMON ⇒ sends `RELEASE`; FILE ⇒ wraps `memory_jobserver::MemoryReservation`;
/// INERT ⇒ no-op. RAII: released on success, error, AND panic-unwind.
#[must_use = "reservation frees its bytes on drop; bind it for the solve's lifetime"]
pub struct Reservation {
    inner: ReservationKind,
}

/// Fail-closed admission error from a provisioned coordinator domain.
/// Unconfigured standalone use still returns an inert reservation successfully;
/// this error means a caller must stop before spawning solver work.
#[derive(Debug, thiserror::Error)]
pub enum ReservationError {
    /// The selected Unix-socket authority did not complete a valid grant.
    #[cfg(unix)]
    #[error("configured trustd admission failed: {0}")]
    Daemon(String),
    /// The selected file-ledger authority could not safely admit the request.
    #[error(transparent)]
    File(#[from] MemoryJobserverError),
}

enum ReservationKind {
    /// Granted by the daemon (rung 2). In-process work sends RELEASE on Drop;
    /// child-bound work closes its stream and lets descendant-wide EOF release.
    #[cfg(unix)]
    Daemon {
        stream: UnixStream,
        token: u64,
        bytes: u64,
        owner_pid: u32,
        /// False after the owning connection has been inherited by an external
        /// child. From then on, kernel EOF across every descendant copy is the
        /// only safe release authority.
        explicit_release_on_drop: bool,
    },
    /// Granted by the flock file bucket (rung 3). Releases via inner Drop.
    File(MemoryReservation),
    /// Inert (rung 1 only): no configured authority, so no-op.
    Inert,
}

impl Reservation {
    /// An inert reservation for an unconfigured standalone caller.
    #[must_use]
    pub fn inert() -> Self {
        Self { inner: ReservationKind::Inert }
    }

    /// Whether this reservation actually holds bytes (daemon-granted or
    /// file-active). A daemon sentinel grant (token 0, bytes 0) is NOT active.
    #[must_use]
    pub fn is_active(&self) -> bool {
        match &self.inner {
            #[cfg(unix)]
            ReservationKind::Daemon { token, bytes, .. } => *token != 0 && *bytes > 0,
            ReservationKind::File(r) => r.is_active(),
            ReservationKind::Inert => false,
        }
    }

    /// The number of bytes this reservation holds (0 when inert).
    #[must_use]
    pub fn bytes(&self) -> u64 {
        match &self.inner {
            #[cfg(unix)]
            ReservationKind::Daemon { bytes, .. } => *bytes,
            ReservationKind::File(r) => r.bytes(),
            ReservationKind::Inert => 0,
        }
    }

    /// Couple a forthcoming external child's lifetime to this reservation.
    ///
    /// The daemon lane installs a pre-exec duplicate of the owning Unix stream.
    /// If the parent is killed without sending RELEASE, kernel EOF therefore
    /// cannot reach trustd until the solver (and inheriting descendants) exits.
    /// Normal cleanup must still terminate/reap the solver group before dropping
    /// this reservation. An active file-ledger row is owned by the parent PID and
    /// cannot be transferred atomically through `Command::spawn`; reject that
    /// lane before process creation rather than undercount after a parent crash.
    pub fn configure_child_lifetime_guard(
        &mut self,
        command: &mut std::process::Command,
    ) -> Result<(), String> {
        match &mut self.inner {
            #[cfg(unix)]
            ReservationKind::Daemon { stream, explicit_release_on_drop, .. } => {
                inherit_fd_across_exec(command, stream.as_raw_fd()).map_err(|error| {
                    format!("could not retain the daemon lifetime descriptor for child spawn: {error}")
                })?;
                // Even normal parent cleanup must not send RELEASE after the
                // child boundary is configured. A solver may leave descendants
                // running after its leader is reaped, and group SIGKILL can take
                // time to finish. Closing our stream lets trustd reclaim only on
                // actual EOF from all inherited descriptor copies.
                *explicit_release_on_drop = false;
                Ok(())
            }
            ReservationKind::File(reservation) if reservation.is_active() => Err(
                "the file memory authority cannot atomically bind its parent-PID row to an external solver; configure the authenticated trustd socket authority"
                    .to_string(),
            ),
            ReservationKind::File(_) | ReservationKind::Inert => Ok(()),
        }
    }
}

/// First duplicate `fd` with CLOEXEC in the parent and move that owned descriptor
/// into the Command's pre-exec closure. The Command can therefore safely outlive
/// the Reservation before spawn without a stale numeric fd being closed/reused.
/// A caller must drop the one-shot Command immediately after spawning so this
/// parent-only staging copy cannot delay EOF after the child exits. In the child,
/// duplicate the stable fd without CLOEXEC immediately before exec; the stable
/// original closes on exec. There is never a process-wide inheritable-FD window.
#[cfg(unix)]
fn inherit_fd_across_exec(
    command: &mut std::process::Command,
    fd: std::os::fd::RawFd,
) -> std::io::Result<()> {
    use std::os::unix::process::CommandExt as _;

    let stable_fd = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if stable_fd < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let stable_fd = unsafe { OwnedFd::from_raw_fd(stable_fd) };
    unsafe {
        command.pre_exec(move || {
            let duplicated = libc::fcntl(stable_fd.as_raw_fd(), libc::F_DUPFD, 3);
            if duplicated < 0 { Err(std::io::Error::last_os_error()) } else { Ok(()) }
        });
    }
    Ok(())
}

impl std::fmt::Debug for Reservation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match &self.inner {
            #[cfg(unix)]
            ReservationKind::Daemon { token, bytes, .. } => {
                format!("Daemon{{token:{token},bytes:{bytes}}}")
            }
            ReservationKind::File(r) => format!("File{{active:{}}}", r.is_active()),
            ReservationKind::Inert => "Inert".to_string(),
        };
        f.debug_struct("Reservation").field("inner", &kind).finish()
    }
}

impl Drop for Reservation {
    fn drop(&mut self) {
        match &mut self.inner {
            // In-process work makes a best-effort RELEASE; closing the owning
            // stream is the fallback if that frame fails. Child-bound work never
            // sends RELEASE: dropping only the parent copy lets kernel EOF wait
            // for every inherited descendant. The File arm's inner Drop fires
            // automatically.
            #[cfg(unix)]
            ReservationKind::Daemon {
                stream, token, owner_pid, explicit_release_on_drop, ..
            } => {
                // A forked copy is not the reservation owner. Releasing from it
                // could undercount work still running in the parent; retaining
                // until the owner's RELEASE/EOF is the conservative outcome.
                if *explicit_release_on_drop
                    && *token != 0
                    && reservation_owner_may_release(*owner_pid)
                {
                    let _ = writeln!(stream, "RELEASE {token}");
                    let _ = stream.flush();
                }
            }
            ReservationKind::File(_) | ReservationKind::Inert => {}
        }
    }
}

fn reservation_owner_may_release(owner_pid: u32) -> bool {
    owner_pid == std::process::id()
}

/// Acquire `bytes` against the aggregate budget BEFORE spawning/linking `ay`.
/// Rung selection is transparent to the caller (see module doc). A configured
/// authority failure is returned so the caller can stop before solver spawn.
#[must_use]
pub fn reserve(bytes: u64) -> Result<Reservation, ReservationError> {
    reserve_labeled(bytes, "")
}

/// Result of choosing the optional daemon admission lane. A selected lane is
/// sticky for this reservation attempt: transport or protocol failure cannot
/// cross into the separately-accounted file bucket.
#[cfg(unix)]
enum ConfiguredDaemonAttempt {
    /// No socket lane was provisioned, or it was explicitly disabled before
    /// selection. The caller may select the file lane.
    Unprovisioned,
    /// A configured socket selected the daemon lane. Its result is authoritative:
    /// failure stops the solve and never crosses into the file ledger.
    Selected(Result<Reservation, ReservationError>),
}

#[cfg(unix)]
fn reserve_from_configured_daemon(bytes: u64, label: &str) -> ConfiguredDaemonAttempt {
    reserve_from_configured_daemon_with(bytes, label, OBSERVER_IO_TIMEOUT, machine_budget_bytes)
}

/// [`reserve_from_configured_daemon`] carrying the same two explicit ambient
/// inputs as [`reserve_via_daemon_with`]. Production passes the production
/// constants; only lane *selection* is decided here, and that is unchanged.
#[cfg(unix)]
fn reserve_from_configured_daemon_with<F>(
    bytes: u64,
    label: &str,
    observer_timeout: Duration,
    current_client_budget: F,
) -> ConfiguredDaemonAttempt
where
    F: FnOnce() -> u64,
{
    let configured_socket = sock_path();
    if disabled() {
        return if !matches!(configured_socket, Ok(None)) {
            ConfiguredDaemonAttempt::Selected(Err(ReservationError::Daemon(
                "TRUSTD_DISABLE cannot bypass an already-configured socket authority".to_string(),
            )))
        } else {
            ConfiguredDaemonAttempt::Unprovisioned
        };
    }
    let sock = match configured_socket {
        Ok(Some(sock)) => sock,
        Ok(None) => return ConfiguredDaemonAttempt::Unprovisioned,
        Err(error) => {
            return ConfiguredDaemonAttempt::Selected(Err(ReservationError::Daemon(error)));
        }
    };
    ConfiguredDaemonAttempt::Selected(reserve_via_daemon_with(
        &sock,
        bytes,
        label,
        observer_timeout,
        current_client_budget,
    ))
}

/// `reserve` with an explicit `<label>` (crate name / purpose) for STATUS.
#[must_use]
pub fn reserve_labeled(bytes: u64, label: &str) -> Result<Reservation, ReservationError> {
    // Select the daemon lane once. After a configured socket is selected, every
    // busy, declined, malformed, timed-out, or I/O-failed exchange is returned
    // as an error rather than launching unreserved or crossing into another ledger.
    #[cfg(unix)]
    match reserve_from_configured_daemon(bytes, label) {
        ConfiguredDaemonAttempt::Selected(result) => return result,
        ConfiguredDaemonAttempt::Unprovisioned => {}
    }
    // The flock file bucket is eligible only when no daemon socket lane was
    // provisioned (or daemon use was explicitly disabled before selection).
    // An unconfigured file lane returns an inert reservation; a provisioned
    // ledger failure is explicit and must stop solver launch.
    memory_jobserver::acquire(bytes)
        .map(|reservation| Reservation { inner: ReservationKind::File(reservation) })
        .map_err(ReservationError::from)
}

/// [`reserve_labeled`] against a caller-supplied observational deadline and
/// client budget, for tests that drive the CONFIGURED-socket lane. Test-only:
/// the production entry point is [`reserve_labeled`], which keeps
/// `OBSERVER_IO_TIMEOUT` and `machine_budget_bytes`. Lane selection, stickiness
/// and the file-bucket fallback are the same code as above.
#[cfg(all(unix, test))]
fn reserve_labeled_with<F>(
    bytes: u64,
    label: &str,
    observer_timeout: Duration,
    current_client_budget: F,
) -> Result<Reservation, ReservationError>
where
    F: FnOnce() -> u64,
{
    match reserve_from_configured_daemon_with(bytes, label, observer_timeout, current_client_budget)
    {
        ConfiguredDaemonAttempt::Selected(result) => return result,
        ConfiguredDaemonAttempt::Unprovisioned => {}
    }
    memory_jobserver::acquire(bytes)
        .map(|reservation| Reservation { inner: ReservationKind::File(reservation) })
        .map_err(ReservationError::from)
}

/// The per-job memory ceiling (bytes) one verification worker should reserve,
/// derived from the shared budget / parallelism (mirrors the subprocess path's
/// `effective_memory_limit_mb`). `Ok(0)` only when no coordinator is configured.
/// An active domain with no derivable budget fails closed before solver spawn.
/// Exposed so the in-compiler native-verify path can reserve without reaching
/// into `memory_jobserver`.
#[must_use]
pub fn default_reservation_bytes() -> Result<u64, ReservationError> {
    #[cfg(unix)]
    let daemon_socket = sock_path().map_err(ReservationError::Daemon)?;
    #[cfg(unix)]
    let daemon_configured = daemon_socket.is_some();
    #[cfg(not(unix))]
    let daemon_configured = false;
    let file_configured = memory_jobserver::is_active();

    if !daemon_configured && !file_configured {
        return Ok(0);
    }
    #[cfg(unix)]
    if daemon_configured && disabled() {
        return Err(ReservationError::Daemon(
            "TRUSTD_DISABLE cannot bypass an already-configured socket authority".to_string(),
        ));
    }
    if let Some(mb) = memory_jobserver::default_per_job_limit_mb() {
        return Ok(mb.saturating_mul(1024 * 1024));
    }
    #[cfg(unix)]
    if daemon_configured {
        return Err(ReservationError::Daemon(
            "the host physical-memory budget could not be derived".to_string(),
        ));
    }
    if file_configured {
        return Err(ReservationError::File(MemoryJobserverError::BudgetUnavailable));
    }
    Ok(0)
}

/// Explicit release (RAII `Drop` calls this; exposed for symmetry / future
/// trustc). `drop(r)` is equivalent.
pub fn release(r: Reservation) {
    drop(r);
}

/// Try the selected daemon: connect, verify its current STATUS ceiling against
/// this client's effective-memory domain, then RESERVE on the same connection.
/// Only a nonzero GRANTED token succeeds. A broader-cgroup daemon, DEGRADED,
/// busy, transport failure, malformed reply, or sentinel grant for a nonzero
/// request all stop before solver spawn.
#[cfg(unix)]
fn reserve_via_daemon(
    sock: &Path,
    bytes: u64,
    label: &str,
) -> Result<Reservation, ReservationError> {
    reserve_via_daemon_with(sock, bytes, label, OBSERVER_IO_TIMEOUT, machine_budget_bytes)
}

/// [`reserve_via_daemon`] with its two *ambient* inputs made explicit: the
/// observational deadline the STATUS preflight runs under, and the client's
/// current effective-memory budget. Production passes `OBSERVER_IO_TIMEOUT` and
/// `machine_budget_bytes`, so every shipped path is unchanged.
///
/// The seam exists for the same reason
/// [`lease_compatible_daemon_probe_until`] has one: a test that wants to
/// prove a *protocol* property must not also be measuring host scheduling, and
/// must not read a process-global budget cache that a sibling test can rewrite
/// between this function's two observations of it.
#[cfg(unix)]
fn reserve_via_daemon_with<F>(
    sock: &Path,
    bytes: u64,
    label: &str,
    observer_timeout: Duration,
    current_client_budget: F,
) -> Result<Reservation, ReservationError>
where
    F: FnOnce() -> u64,
{
    reserve_via_daemon_with_peer(sock, bytes, label, observer_timeout, None, current_client_budget)
}

#[cfg(unix)]
fn reserve_via_daemon_with_peer<F>(
    sock: &Path,
    bytes: u64,
    label: &str,
    observer_timeout: Duration,
    expected_peer_pid: Option<u32>,
    current_client_budget: F,
) -> Result<Reservation, ReservationError>
where
    F: FnOnce() -> u64,
{
    let status_deadline = Instant::now().checked_add(observer_timeout).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until_with_pid(sock, status_deadline, expected_peer_pid)
        .map_err(|error| {
            ReservationError::Daemon(format!(
                "could not connect to selected endpoint {}: {error}",
                sock.display()
            ))
        })?;
    write_line_until(&mut stream, "STATUS", status_deadline).map_err(|error| {
        ReservationError::Daemon(format!("could not send STATUS preflight: {error}"))
    })?;
    let status_reply = read_one_line_until(&stream, status_deadline).ok_or_else(|| {
        ReservationError::Daemon(
            "selected endpoint did not return one complete STATUS reply before the deadline"
                .to_string(),
        )
    })?;
    let status = serde_json::from_str::<DaemonStatus>(status_reply.trim()).map_err(|_| {
        ReservationError::Daemon(format!(
            "selected endpoint returned an invalid STATUS reply: {:?}",
            status_reply.trim()
        ))
    })?;
    if !status.has_valid_invariants() {
        return Err(ReservationError::Daemon(
            "selected endpoint returned a semantically contradictory STATUS reply".to_string(),
        ));
    }
    let client_budget = current_client_budget();
    if !daemon_budget_is_acceptable(&status, client_budget) {
        return Err(ReservationError::Daemon(format!(
            "selected endpoint budget {} is not usable from this client's current effective-memory budget {}",
            status.budget_bytes, client_budget
        )));
    }
    if bytes > client_budget {
        return Err(ReservationError::Daemon(format!(
            "requested reservation {bytes} exceeds this client's current effective-memory budget {client_budget}"
        )));
    }

    let deadline = Instant::now()
        .checked_add(acquire_deadline().saturating_add(CLIENT_IO_MARGIN))
        .unwrap_or_else(Instant::now);
    let pid = std::process::id();
    // Strip any newline so a multi-token label cannot break line framing.
    let mut label = label.replace(['\n', '\r'], " ");
    truncate_label(&mut label);
    write_line_until(&mut stream, &format!("RESERVE {bytes} {pid} {label}"), deadline).map_err(
        |error| ReservationError::Daemon(format!("could not send RESERVE request: {error}")),
    )?;
    let reply = read_one_line_until(&stream, deadline).ok_or_else(|| {
        ReservationError::Daemon(
            "selected endpoint did not return one complete reply before the deadline".to_string(),
        )
    })?;
    let reply = reply.trim();
    if let Some(tok) = reply.strip_prefix("GRANTED ") {
        let token: u64 = tok.trim().parse().map_err(|_| {
            ReservationError::Daemon(
                "selected endpoint returned an invalid grant token".to_string(),
            )
        })?;
        if token == 0 && bytes == 0 {
            // The selected authority was still authenticated and exercised; the
            // sentinel holds no ledger capacity and may close immediately.
            return Ok(Reservation::inert());
        }
        if token == 0 {
            return Err(ReservationError::Daemon(
                "selected endpoint returned a zero-token grant for a nonzero request".to_string(),
            ));
        }
        if bytes == 0 {
            return Err(ReservationError::Daemon(
                "selected endpoint returned a nonzero grant for a zero-byte request".to_string(),
            ));
        }
        // RELEASE is best-effort but must also remain bounded if the daemon
        // wedges after granting this reservation.
        let _ = stream.set_write_timeout(Some(observer_timeout));
        Ok(Reservation {
            inner: ReservationKind::Daemon {
                stream,
                token,
                bytes,
                owner_pid: pid,
                explicit_release_on_drop: true,
            },
        })
    } else if reply == "DEGRADED" {
        Err(ReservationError::Daemon(
            "selected endpoint declined the reservation within its admission deadline".to_string(),
        ))
    } else {
        Err(ReservationError::Daemon(format!(
            "selected endpoint returned an invalid reservation reply: {reply:?}"
        )))
    }
}

/// Reserve directly against an explicit daemon endpoint, without falling back to
/// the file bucket. The same private-endpoint checks and admission deadline used
/// by worker traffic apply. Release the returned reservation with [`release`] or
/// by dropping it.
#[must_use]
#[cfg(unix)]
pub fn reserve_labeled_at(
    sock: &Path,
    bytes: u64,
    label: &str,
) -> Result<Reservation, ReservationError> {
    reserve_via_daemon(sock, bytes, label)
}

/// [`reserve_labeled_at`] against a caller-supplied observational deadline and
/// client budget. Test-only: it exists so a protocol test can pin both ambient
/// inputs it does not mean to measure. Production reserves through
/// [`reserve_labeled_at`], which keeps `OBSERVER_IO_TIMEOUT` and
/// `machine_budget_bytes`.
#[cfg(all(unix, test))]
fn reserve_labeled_at_with<F>(
    sock: &Path,
    bytes: u64,
    label: &str,
    observer_timeout: Duration,
    current_client_budget: F,
) -> Result<Reservation, ReservationError>
where
    F: FnOnce() -> u64,
{
    reserve_via_daemon_with(sock, bytes, label, observer_timeout, current_client_budget)
}

/// Fetch + parse the daemon STATUS (rung 2 only). `None` when no daemon is
/// reachable (the menubar / diagnostics caller shows "daemon off"). Pure read —
/// never sends RESERVE/RELEASE, so an observer cannot perturb admission.
#[must_use]
pub fn status() -> Option<DaemonStatus> {
    // Daemon STATUS rides the Unix-socket transport; no daemon exists on non-Unix
    // hosts, so report "daemon off" (None) — the documented rung-1 observation.
    #[cfg(unix)]
    {
        let sock = sock_path().ok()??;
        status_at(&sock)
    }
    #[cfg(not(unix))]
    {
        None
    }
}

/// `status()` against an explicit socket path (used by tests + the menubar).
#[must_use]
#[cfg(unix)]
pub fn status_at(sock: &Path) -> Option<DaemonStatus> {
    status_at_with_peer(sock, None)
}

#[cfg(unix)]
fn status_at_with_peer(sock: &Path, expected_peer_pid: Option<u32>) -> Option<DaemonStatus> {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until_with_pid(sock, deadline, expected_peer_pid).ok()?;
    write_line_until(&mut stream, "STATUS", deadline).ok()?;
    let line = read_one_line_until(&stream, deadline)?;
    let status: DaemonStatus = serde_json::from_str(line.trim()).ok()?;
    status.has_valid_invariants().then_some(status)
}

/// A fixed per-euid socket can be reached by processes in different Linux
/// cgroups. A client may safely participate only when the daemon's monotonic
/// ceiling is nonzero and no larger than the client's current effective-memory
/// budget. The daemon may be more conservative than the client, never broader.
fn daemon_budget_is_acceptable(status: &DaemonStatus, client_budget: u64) -> bool {
    status.has_valid_invariants()
        && client_budget != 0
        && status.budget_bytes != 0
        && status.budget_bytes <= client_budget
}

/// Fetch the daemon's closed build/runtime identity. This is public for release
/// diagnostics and process-level contract tests; STATUS observers need not call
/// it and the STATUS v1 schema remains unchanged.
#[must_use]
#[cfg(unix)]
pub fn identity_at(sock: &Path) -> Option<DaemonIdentity> {
    identity_at_with_peer(sock, None)
}

#[cfg(unix)]
fn identity_at_with_peer(sock: &Path, expected_peer_pid: Option<u32>) -> Option<DaemonIdentity> {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until_with_pid(sock, deadline, expected_peer_pid).ok()?;
    write_line_until(&mut stream, "IDENTITY", deadline).ok()?;
    let line = read_one_line_until(&stream, deadline)?;
    let identity: DaemonIdentity = serde_json::from_str(line.trim()).ok()?;
    identity.has_valid_invariants().then_some(identity)
}

/// Adopt the daemon at `sock` for the caller's session: authenticate it as
/// [`compatible_daemon_until_with_peer_and_budget_source`] does, then take a
/// session lease on that same connection, so the daemon held is exactly the
/// one whose identity and budget were checked. `None` when it is absent,
/// incompatible, or closing (one past its CLEAN shutdown proof answers
/// DEGRADED); the launcher then establishes a successor.
#[cfg(unix)]
fn lease_compatible_daemon_at(sock: &Path, expected: &DaemonIdentity) -> Option<DaemonLease> {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    lease_compatible_daemon_until(sock, expected, deadline).ok()
}

/// Why one readiness probe of an endpoint did not adopt it. Only the
/// launcher whose child lost the stable-ownership race reads the cause
/// ([`wait_for_spawned_daemon`]); every other caller sees `None` either way.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProbeMiss {
    /// Nothing serves the path yet: no socket there (`NotFound`), a stale one
    /// (`ECONNREFUSED`), or one replaced while connecting. A live owner that
    /// holds the stable lock but has not yet reclaimed and published the
    /// endpoint looks exactly like this ([`bind_owned_socket`]), so this, and
    /// only this, may be probed again.
    NotServing,
    /// The endpoint answered the IDENTITY request with a first line that is
    /// exactly the framed line [`BUSY_REPLY`]: a live `trustd` at its
    /// connection limit ([`reject_busy_connection`]), which then shuts down
    /// its write half. Nothing after that line is read: a busy answer is never
    /// adopted, so what follows it cannot matter. A capacity answer, not an
    /// identity: it says nothing about who holds the stable lock, so it is
    /// never adopted and never read as anyone's identity. Only the lost-race
    /// wait reads it apart from [`ProbeMiss::Refused`] ([`wait_for_live_owner`]:
    /// tried again, like [`ProbeMiss::NotServing`], until the same deadline);
    /// every other caller sees `None` either way, and the solver-launch path
    /// ([`reserve_via_daemon`]) never consults it (TRUSTD-LOST-RACE-2).
    Busy,
    /// A definite answer, or a failure after something accepted the
    /// connection: a foreign or invalid IDENTITY, an invalid or unacceptable
    /// STATUS, a refused LEASE, an exchange that closed or timed out, any
    /// reply that is not exactly [`BUSY_REPLY`] where a busy answer would come,
    /// or an endpoint that is not a private socket of this euid. Never retried
    /// into adoption.
    Refused,
}

/// The one line a `trustd` at its connection limit sends before it closes
/// ([`reject_busy_connection`], framed with `\n`). Matched exactly, with no
/// trimming: `ERR busy` with anything before or after it on the line, or
/// without its newline, is not this answer ([`ProbeMiss::Busy`]).
#[cfg(unix)]
const BUSY_REPLY: &str = "ERR busy";

#[cfg(unix)]
impl ProbeMiss {
    /// Classify a failed [`connect_trusted_until_with_pid`]. A replaced socket
    /// is the publication instant itself (the owner reclaimed the stale path
    /// and renamed its own into place between the two identity checks): the
    /// next probe authenticates whatever is there from the start.
    fn of_connect(error: &std::io::Error) -> Self {
        if stale_connect_error(error)
            || matches!(
                error.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::ConnectionAborted
            )
        {
            Self::NotServing
        } else {
            Self::Refused
        }
    }
}

#[cfg(unix)]
fn lease_compatible_daemon_until(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
) -> Result<DaemonLease, ProbeMiss> {
    lease_compatible_daemon_probe_until(sock, expected, deadline, machine_budget_bytes)
}

#[cfg(all(unix, test))]
fn lease_compatible_daemon_until_with_budget_source<F>(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
    current_client_budget: F,
) -> Option<DaemonLease>
where
    F: FnOnce() -> u64,
{
    lease_compatible_daemon_probe_until(sock, expected, deadline, current_client_budget).ok()
}

/// Lease the exact, budget-compatible daemon at `sock`, or say why not
/// ([`ProbeMiss`]). `current_client_budget` is the test seam; production
/// passes `machine_budget_bytes` ([`lease_compatible_daemon_until`]).
#[cfg(unix)]
fn lease_compatible_daemon_probe_until<F>(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
    current_client_budget: F,
) -> Result<DaemonLease, ProbeMiss>
where
    F: FnOnce() -> u64,
{
    let mut stream =
        compatible_connection_probe_until(sock, expected, deadline, None, current_client_budget)?;
    write_line_until(&mut stream, "LEASE", deadline).map_err(|_| ProbeMiss::Refused)?;
    let reply = read_one_line_until(&stream, deadline).ok_or(ProbeMiss::Refused)?;
    if reply.trim() == "LEASED" {
        Ok(DaemonLease { _connection: stream })
    } else {
        Err(ProbeMiss::Refused)
    }
}

#[cfg(unix)]
fn compatible_daemon_until_with_peer_and_budget_source<F>(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
    expected_peer_pid: Option<u32>,
    current_client_budget: F,
) -> bool
where
    F: FnOnce() -> u64,
{
    compatible_connection_until_with_peer_and_budget_source(
        sock,
        expected,
        deadline,
        expected_peer_pid,
        current_client_budget,
    )
    .is_some()
}

/// The connection behind [`compatible_daemon_until_with_peer_and_budget_source`]:
/// IDENTITY and STATUS on one stream, returned only when both pass, so a
/// caller can go on to act on exactly the daemon it authenticated.
#[cfg(unix)]
fn compatible_connection_until_with_peer_and_budget_source<F>(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
    expected_peer_pid: Option<u32>,
    current_client_budget: F,
) -> Option<UnixStream>
where
    F: FnOnce() -> u64,
{
    compatible_connection_probe_until(
        sock,
        expected,
        deadline,
        expected_peer_pid,
        current_client_budget,
    )
    .ok()
}

/// [`compatible_connection_until_with_peer_and_budget_source`], saying why it
/// did not authenticate ([`ProbeMiss`]): only a failed connect can be
/// [`ProbeMiss::NotServing`]; only an IDENTITY reply that is exactly
/// [`BUSY_REPLY`] is [`ProbeMiss::Busy`] (a saturated daemon rejects at accept,
/// so its answer is the first line; the same line in reply to STATUS is no
/// such answer); everything else after the connect is a definite refusal.
#[cfg(unix)]
fn compatible_connection_probe_until<F>(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
    expected_peer_pid: Option<u32>,
    current_client_budget: F,
) -> Result<UnixStream, ProbeMiss>
where
    F: FnOnce() -> u64,
{
    use ProbeMiss::Refused;
    let mut stream = connect_trusted_until_with_pid(sock, deadline, expected_peer_pid)
        .map_err(|error| ProbeMiss::of_connect(&error))?;
    write_line_until(&mut stream, "IDENTITY", deadline).map_err(|_| Refused)?;
    let identity_line = read_one_line_until(&stream, deadline).ok_or(Refused)?;
    if identity_line == BUSY_REPLY {
        return Err(ProbeMiss::Busy);
    }
    let identity =
        serde_json::from_str::<DaemonIdentity>(identity_line.trim()).map_err(|_| Refused)?;
    if !identity.has_valid_invariants() || &identity != expected {
        return Err(Refused);
    }

    write_line_until(&mut stream, "STATUS", deadline).map_err(|_| Refused)?;
    let status_line = read_one_line_until(&stream, deadline).ok_or(Refused)?;
    let status = serde_json::from_str::<DaemonStatus>(status_line.trim()).map_err(|_| Refused)?;
    // Observe after the protocol exchange so a recently lowered cgroup ceiling
    // is compared as late as practical before adopting this daemon.
    if daemon_budget_is_acceptable(&status, current_client_budget())
        && expected_peer_pid.is_none_or(|pid| require_live_unreaped_child(pid).is_ok())
    {
        Ok(stream)
    } else {
        Err(Refused)
    }
}

/// Return whether `sock` reports the expected executable digest and build
/// identity, and has an acceptable STATUS. This does not authenticate the
/// serving process; release smoke uses [`daemon_matches_executable_from_pid`].
#[must_use]
#[cfg(unix)]
pub fn daemon_matches_executable(sock: &Path, executable: &Path) -> bool {
    daemon_identity_for_executable(executable)
        .is_ok_and(|expected| daemon_matches_bound_identity(sock, executable, &expected))
}

/// Return whether `sock` reports an explicitly supplied build identity and a
/// digest matching the exact bytes at `executable`. This is self-report, not
/// an OS process-identity check.
///
/// This is the cross-version companion to [`daemon_matches_executable`].
/// Diagnostic code may inspect a candidate toolchain whose
/// release and commit intentionally differ from the client library doing the
/// inspection. The caller-supplied identity is accepted only after its closed
/// schema validates and its executable digest is independently recomputed.
#[must_use]
#[cfg(unix)]
pub fn daemon_matches_bound_identity(
    sock: &Path,
    executable: &Path,
    expected: &DaemonIdentity,
) -> bool {
    daemon_matches_bound_identity_with_peer(sock, executable, expected, None)
}

/// Like [`daemon_matches_executable`], but every connected socket must name a
/// live, unreaped direct child of the caller. A matching protocol self-report
/// or a matching peer PID without that child is insufficient for release evidence.
#[must_use]
#[cfg(unix)]
pub fn daemon_matches_executable_from_pid(
    sock: &Path,
    executable: &Path,
    spawned_child_pid: u32,
) -> bool {
    daemon_identity_for_executable(executable).is_ok_and(|expected| {
        daemon_matches_bound_identity_with_peer(
            sock,
            executable,
            &expected,
            Some(spawned_child_pid),
        )
    })
}

#[cfg(unix)]
fn daemon_matches_bound_identity_with_peer(
    sock: &Path,
    executable: &Path,
    expected: &DaemonIdentity,
    expected_peer_pid: Option<u32>,
) -> bool {
    expected.has_valid_invariants()
        && executable_sha256(executable).is_ok_and(|digest| digest == expected.executable_sha256)
        && {
            let deadline =
                Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
            compatible_daemon_until_with_peer_and_budget_source(
                sock,
                expected,
                deadline,
                expected_peer_pid,
                machine_budget_bytes,
            )
        }
}

/// A live session's hold on the trustd it selected, returned by
/// [`ensure_daemon`]. While it is alive the daemon takes no idle shutdown, so
/// every unit the session launches finds the authority the session exported
/// to it, however long a compile runs before its first admission. The hold is
/// the connection itself: dropping the lease, or the kernel closing its
/// descriptor when the holder exits by any path, SIGKILL included, ends it,
/// and the daemon's [`IDLE_TIMEOUT`] starts then. The descriptor is
/// close-on-exec, so a child the holder spawns later does not inherit the
/// hold; on macOS the flag follows `socket(2)` by one `fcntl`, and a child
/// another thread spawns inside that window does (`connect_unix_until`).
#[cfg(unix)]
#[derive(Debug)]
#[must_use = "the daemon is held only while its lease is alive; keep it for the session's life"]
pub struct DaemonLease {
    _connection: UnixStream,
}

/// A bounded, diagnosable failure to establish the selected same-sysroot
/// `trustd` authority.
#[cfg(unix)]
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum EnsureDaemonError {
    #[error("{DISABLE_ENV}=1 disables trustd startup")]
    Disabled,
    #[error(
        "could not resolve the current executable while selecting its trustd sibling: {source}"
    )]
    CurrentExecutable {
        #[source]
        source: std::io::Error,
    },
    #[error(
        "the selected executable {executable} has no regular, executable, non-symlink trustd sibling"
    )]
    SiblingUnavailable { executable: String },
    #[error("could not authorize the same-sysroot trustd executable {executable}: {source}")]
    ExecutableAuthority {
        executable: String,
        #[source]
        source: std::io::Error,
    },
    #[error("could not derive the closed runtime identity for trustd {executable}: {source}")]
    Identity {
        executable: String,
        #[source]
        source: std::io::Error,
    },
    #[error("could not spawn the same-sysroot trustd {executable}: {source}")]
    Spawn {
        executable: String,
        #[source]
        source: std::io::Error,
    },
    #[error("could not inspect the spawned trustd {executable}: {source}")]
    ChildStatus {
        executable: String,
        #[source]
        source: std::io::Error,
    },
    #[error(
        "same-sysroot trustd {executable} exited before exact-identity readiness with {status}; bounded stderr: {stderr}"
    )]
    EarlyExit { executable: String, status: std::process::ExitStatus, stderr: String },
    #[error(
        "same-sysroot trustd {executable} did not establish exact-identity readiness within {timeout:?}"
    )]
    ReadinessTimeout { executable: String, timeout: Duration },
}

#[cfg(unix)]
fn capture_spawned_stderr(mut stderr: std::process::ChildStderr) -> thread::JoinHandle<String> {
    thread::spawn(move || {
        let mut retained = Vec::with_capacity(MAX_SPAWN_STDERR_BYTES);
        let mut total = 0usize;
        let mut read_error = None;
        let mut chunk = [0u8; 4096];
        loop {
            match stderr.read(&mut chunk) {
                Ok(0) => break,
                Ok(count) => {
                    total = total.saturating_add(count);
                    let remaining = MAX_SPAWN_STDERR_BYTES.saturating_sub(retained.len());
                    retained.extend_from_slice(&chunk[..count.min(remaining)]);
                }
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(error) => {
                    read_error = Some(error);
                    break;
                }
            }
        }
        let mut diagnostic = String::from_utf8_lossy(&retained).into_owned();
        if total > retained.len() {
            diagnostic.push_str(&format!(
                "\n[stderr truncated after {} bytes; {} bytes observed]",
                retained.len(),
                total
            ));
        }
        if let Some(error) = read_error {
            diagnostic.push_str(&format!("\n[stderr read failed: {error}]"));
        }
        if diagnostic.is_empty() {
            diagnostic.push_str("<empty>");
        }
        diagnostic
    })
}

#[cfg(unix)]
fn finish_spawned_stderr(reader: thread::JoinHandle<String>) -> String {
    reader.join().unwrap_or_else(|_| "<stderr reader panicked>".to_string())
}

#[cfg(unix)]
fn reap_spawned_child_in_background(
    mut child: std::process::Child,
    stderr_reader: thread::JoinHandle<String>,
) {
    thread::spawn(move || {
        let _ = child.wait();
        let _ = stderr_reader.join();
    });
}

/// What became of one spawned `trustd`, short of a refusal.
#[cfg(unix)]
#[derive(Debug)]
enum SpawnedDaemon<T> {
    /// The endpoint is ready and held (a lease, in production).
    Ready(T),
    /// The child lost the stable-ownership race ([`OWNED_ELSEWHERE`]), and the
    /// owner it lost to then released the stable lock without ever serving the
    /// endpoint: it exited during startup (a refused epoch, a possibly-live
    /// socket it would not reclaim, a crash), or published and died before it
    /// answered ([`REFUSING_OWNER_RELEASE_GRACE`]). Nothing will serve, so the
    /// launcher may spawn once more ([`spawn_until_adopted`]).
    OwnerVanished { status: std::process::ExitStatus, stderr: String },
}

/// How a launcher whose child lost the stable-ownership race
/// ([`OWNED_ELSEWHERE`]) waits for the live owner.
#[cfg(unix)]
struct LostRaceWait<'a> {
    /// How long the owner has to serve an exact-identity lease
    /// ([`LIVE_OWNER_ADOPT_TIMEOUT`] in production).
    window: Duration,
    /// `true` only when the stable lock is definitely free, so the owner has
    /// exited ([`stable_owner_released`]). Anything uncertain is `false`, and
    /// the wait runs on to its deadline.
    owner_released: &'a mut dyn FnMut() -> bool,
}

/// Poll `is_ready` until it yields the ready daemon's handle (a lease, in
/// production), the child exits, or `timeout` passes.
///
/// A child that exits naming a live owner ([`OWNED_ELSEWHERE`]) hands the wait
/// to that owner ([`wait_for_live_owner`]). Any other early exit gets one short
/// probe inside the readiness bound, and then its
/// [`EnsureDaemonError::EarlyExit`].
#[cfg(unix)]
fn wait_for_spawned_daemon<F, T>(
    mut child: std::process::Child,
    stderr_reader: thread::JoinHandle<String>,
    executable: &Path,
    timeout: Duration,
    lost_race: LostRaceWait<'_>,
    mut is_ready: F,
) -> Result<SpawnedDaemon<T>, EnsureDaemonError>
where
    F: FnMut(Instant) -> Result<T, ProbeMiss>,
{
    let executable = executable.display().to_string();
    let ready_deadline = Instant::now().checked_add(timeout).unwrap_or_else(Instant::now);
    loop {
        let probe_deadline = Instant::now()
            .checked_add(OBSERVER_IO_TIMEOUT)
            .unwrap_or(ready_deadline)
            .min(ready_deadline);
        if let Ok(ready) = is_ready(probe_deadline) {
            reap_spawned_child_in_background(child, stderr_reader);
            return Ok(SpawnedDaemon::Ready(ready));
        }
        match child.try_wait() {
            Ok(Some(status)) => {
                // Another exact same-sysroot launcher may have won the stable
                // ownership race while this child exited with AddrInUse. The
                // child has exited, so its stderr is complete: read it first.
                // A child that names a live owner leaves adoption as the only
                // way on ([`wait_for_live_owner`]); any other exit keeps the
                // short probe inside the readiness bound.
                let stderr = finish_spawned_stderr(stderr_reader);
                if stderr.contains(OWNED_ELSEWHERE) {
                    return wait_for_live_owner(
                        executable,
                        status,
                        stderr,
                        ready_deadline,
                        lost_race,
                        is_ready,
                    );
                }
                let probe_deadline = Instant::now()
                    .checked_add(OBSERVER_IO_TIMEOUT)
                    .unwrap_or(ready_deadline)
                    .min(ready_deadline);
                if let Ok(ready) = is_ready(probe_deadline) {
                    return Ok(SpawnedDaemon::Ready(ready));
                }
                return Err(EnsureDaemonError::EarlyExit { executable, status, stderr });
            }
            Ok(None) => {}
            Err(source) => {
                reap_spawned_child_in_background(child, stderr_reader);
                return Err(EnsureDaemonError::ChildStatus { executable, source });
            }
        }

        let remaining = ready_deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            reap_spawned_child_in_background(child, stderr_reader);
            return Err(EnsureDaemonError::ReadinessTimeout { executable, timeout });
        }
        thread::sleep(SPAWN_POLL_INTERVAL.min(remaining));
    }
}

/// The spawned child exited naming a live owner ([`OWNED_ELSEWHERE`]): that
/// owner holds the stable lock, so adopting it is the only way this run can
/// proceed. It may be slow to answer (each try is bounded by the whole
/// window, not [`OBSERVER_IO_TIMEOUT`]) or not yet serving: [`bind_owned_socket`]
/// takes the lock BEFORE it reclaims a stale socket and publishes its own,
/// so until then the path is missing or refuses the connection. While that is
/// all a try learns ([`ProbeMiss::NotServing`]), try again every
/// [`SPAWN_POLL_INTERVAL`] until the deadline. A live owner at its connection
/// limit ([`ProbeMiss::Busy`], TRUSTD-LOST-RACE-2) is tried again exactly the
/// same way: `ERR busy` says the owner has no free slot, not who it is, so it
/// is no answer to the identity question this wait asks. Both share the one
/// deadline (an owner still busy, or still unpublished, when it passes is
/// refused then with the child's [`EnsureDaemonError::EarlyExit`]: not at its
/// first busy answer, and with no grace or second window after the deadline),
/// and between tries the owner releasing the lock
/// ends the wait as [`SpawnedDaemon::OwnerVanished`]. The first definite
/// refusal ([`ProbeMiss::Refused`]) is never probed again: it ends the wait
/// with the child's [`EnsureDaemonError::EarlyExit`], unless the stable lock
/// comes free within [`REFUSING_OWNER_RELEASE_GRACE`] (the owner died
/// answering). An owner that released the lock unserved ends it with
/// [`SpawnedDaemon::OwnerVanished`]. Adoption still requires the exact
/// identity, a valid budget and a granted lease, from `is_ready`.
#[cfg(unix)]
fn wait_for_live_owner<F, T>(
    executable: String,
    status: std::process::ExitStatus,
    stderr: String,
    ready_deadline: Instant,
    lost_race: LostRaceWait<'_>,
    mut is_ready: F,
) -> Result<SpawnedDaemon<T>, EnsureDaemonError>
where
    F: FnMut(Instant) -> Result<T, ProbeMiss>,
{
    let LostRaceWait { window, owner_released } = lost_race;
    let deadline = Instant::now().checked_add(window).unwrap_or(ready_deadline).max(ready_deadline);
    loop {
        match is_ready(deadline) {
            Ok(ready) => return Ok(SpawnedDaemon::Ready(ready)),
            Err(ProbeMiss::Refused) => {
                let grace = Instant::now()
                    .checked_add(REFUSING_OWNER_RELEASE_GRACE)
                    .unwrap_or(deadline)
                    .min(deadline);
                if released_by(owner_released, grace) {
                    return Ok(SpawnedDaemon::OwnerVanished { status, stderr });
                }
                break;
            }
            // Not yet serving, or serving at capacity: neither names who holds
            // the lock, so ask again, inside the same deadline.
            Err(ProbeMiss::NotServing | ProbeMiss::Busy) => {}
        }
        if owner_released() {
            return Ok(SpawnedDaemon::OwnerVanished { status, stderr });
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            break;
        }
        thread::sleep(SPAWN_POLL_INTERVAL.min(remaining));
    }
    Err(EnsureDaemonError::EarlyExit { executable, status, stderr })
}

/// Whether `owner_released` says so by `until`, asked every
/// [`SPAWN_POLL_INTERVAL`] and at least once.
#[cfg(unix)]
fn released_by(owner_released: &mut dyn FnMut() -> bool, until: Instant) -> bool {
    loop {
        if owner_released() {
            return true;
        }
        let remaining = until.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return false;
        }
        thread::sleep(SPAWN_POLL_INTERVAL.min(remaining));
    }
}

/// Spawn `trustd` through `spawn` and wait for it ([`wait_for_spawned_daemon`]).
/// When the owner a child lost to vanished unserved
/// ([`SpawnedDaemon::OwnerVanished`]), spawn once more: that child either takes
/// the lock itself or names the live owner it lost to. A second vanished owner
/// is refused as the early exit it is. At most two children, each wait bounded.
#[cfg(unix)]
fn spawn_until_adopted<S, F, T>(
    executable: &Path,
    ready_timeout: Duration,
    adopt_window: Duration,
    mut spawn: S,
    owner_released: &mut dyn FnMut() -> bool,
    mut is_ready: F,
) -> Result<T, EnsureDaemonError>
where
    S: FnMut() -> Result<(std::process::Child, thread::JoinHandle<String>), EnsureDaemonError>,
    F: FnMut(Instant) -> Result<T, ProbeMiss>,
{
    let mut respawned = false;
    loop {
        let (child, stderr_reader) = spawn()?;
        let lost_race = LostRaceWait { window: adopt_window, owner_released: &mut *owner_released };
        match wait_for_spawned_daemon(
            child,
            stderr_reader,
            executable,
            ready_timeout,
            lost_race,
            &mut is_ready,
        )? {
            SpawnedDaemon::Ready(ready) => return Ok(ready),
            SpawnedDaemon::OwnerVanished { .. } if !respawned => respawned = true,
            SpawnedDaemon::OwnerVanished { status, stderr } => {
                return Err(EnsureDaemonError::EarlyExit {
                    executable: executable.display().to_string(),
                    status,
                    stderr,
                });
            }
        }
    }
}

/// Whether nobody holds the stable ownership lock at `sentinel` right now:
/// `true` only when a non-blocking SHARED `flock` is granted, which no live
/// owner allows (each holds it exclusively for its whole life). The shared
/// lock ends when the descriptor closes, before this returns. Anything else (no
/// sentinel, an invalid one, any error) is `false`: unknown is not released.
/// It never creates, writes or repairs the sentinel, and never waits to open
/// it: `O_NONBLOCK`, because a read-only open of a FIFO otherwise waits for a
/// writer with no deadline (and a FIFO is no sentinel). The brief shared lock
/// can only be met while no owner exists; a `trustd` that tries to take
/// ownership in that instant reports [`OWNED_ELSEWHERE`] and its launcher waits
/// as this one does, while this one spawns again ([`spawn_until_adopted`]).
#[cfg(unix)]
fn stable_owner_released(sentinel: &Path) -> bool {
    let Ok(file) = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(sentinel)
    else {
        return false;
    };
    validate_stable_sentinel(&file, sentinel).is_ok()
        && unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_SH | libc::LOCK_NB) } == 0
}

/// The release check [`ensure_daemon`] hands its lost-race wait
/// ([`LostRaceWait::owner_released`]): [`stable_owner_released`] of the stable
/// sentinel that guards `sock`, derived exactly as [`bind_owned_socket`]
/// derives the one it locks (canonical socket path, then
/// [`stable_lock_path_for_socket`]). The sentinel is located on the first call
/// only, so a launcher whose child never lost the race never looks for it; one
/// that cannot be located is never released.
#[cfg(unix)]
fn stable_owner_released_for_socket(sock: &Path) -> impl FnMut() -> bool + '_ {
    let mut sentinel: Option<Option<PathBuf>> = None;
    move || {
        sentinel
            .get_or_insert_with(|| {
                canonical_socket_path(sock)
                    .and_then(|canonical| stable_lock_path_for_socket(&canonical))
                    .ok()
            })
            .as_deref()
            .is_some_and(stable_owner_released)
    }
}

/// Ensure a compatible daemon is listening on `sock`, and hold it for the
/// caller's session. Readiness requires exact packaged-binary
/// [`DaemonIdentity`], a semantically valid, nonzero-budget [`STATUS_VERSION`]
/// response, and a session lease taken on that same connection, not merely a
/// `PONG` from an arbitrary process. Otherwise spawn the packaged `trustd` and
/// identity/status/lease-poll up to [`SPAWN_READY_TIMEOUT`]; a spawned child
/// that lost the ownership race leaves the live owner up to
/// `LIVE_OWNER_ADOPT_TIMEOUT` (60 s) to serve, and an owner that vanished
/// unserved (or died as it refused) costs one more spawn. Every refusal
/// retains its typed cause; a caller that selected this socket domain must not
/// silently launch workers on an independent file authority.
///
/// The returned [`DaemonLease`] is what makes that selection last: a caller
/// exports this socket to workers it launches later, and keeps the lease
/// until none of them can still ask for admission. Without it the daemon idles
/// out [`IDLE_TIMEOUT`] after the last admission, and a unit that compiles
/// longer than that before its first one finds the selected endpoint dead and,
/// fail-closed, refuses every obligation it owns (the 0.11.0 consumer check of
/// 2026-10-19: 129 obligations of one binary refused admission, ECONNREFUSED).
#[cfg(unix)]
pub fn ensure_daemon(sock: &Path) -> Result<DaemonLease, EnsureDaemonError> {
    ensure_daemon_for_client_build(sock, None)
}

/// Admit the same-sysroot daemon for an explicitly selected compiler build.
///
/// A separately built frontend can retain an older compiler and daemon. The
/// caller supplies that compiler's independently bound build identity; the
/// daemon's executable hash and every socket, status, lease and spawn check
/// remain those of the ordinary same-sysroot route. No server response selects
/// the expected build, and this does not change the daemon's own identity.
///
/// # Errors
/// [`ensure_daemon`]'s refusals, including malformed expected build metadata.
#[cfg(unix)]
pub fn ensure_daemon_for_build(
    sock: &Path,
    release: &str,
    commit: &str,
) -> Result<DaemonLease, EnsureDaemonError> {
    ensure_daemon_for_client_build(sock, Some((release, commit)))
}

#[cfg(unix)]
fn client_build_identity(
    mut identity: DaemonIdentity,
    selected: Option<(&str, &str)>,
) -> std::io::Result<DaemonIdentity> {
    if let Some((release, commit)) = selected {
        if release.is_empty()
            || release.len() > 128
            || !release.bytes().all(|b| b.is_ascii_alphanumeric() || b".-+_".contains(&b))
            || commit.len() != 40
            || !commit.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "retained daemon requires an exact release and canonical compiler commit",
            ));
        }
        identity.release = release.to_string();
        identity.commit = commit.to_string();
    }
    Ok(identity)
}

#[cfg(unix)]
fn ensure_daemon_for_client_build(
    sock: &Path,
    selected: Option<(&str, &str)>,
) -> Result<DaemonLease, EnsureDaemonError> {
    if disabled() {
        return Err(EnsureDaemonError::Disabled);
    }
    // Resolve only the trustd packaged beside this executable. An ambient
    // CARGO_HOME/PATH daemon is not part of this toolchain's authenticated
    // identity and must never become its memory-budget authority.
    let (trustd, expected_identity) = resolve_trustd()?;
    let expected_identity =
        client_build_identity(expected_identity, selected).map_err(|source| {
            EnsureDaemonError::Identity { executable: trustd.display().to_string(), source }
        })?;
    // Resolve and hash the exact packaged sibling before accepting any existing
    // endpoint. STATUS compatibility alone is intentionally insufficient. A
    // daemon that refuses the lease has closed admission and is about to exit
    // CLEAN, so it is treated as absent and the spawn below establishes its
    // successor.
    if let Some(lease) = lease_compatible_daemon_at(sock, &expected_identity) {
        return Ok(lease);
    }
    let mut owner_released = stable_owner_released_for_socket(sock);

    // IDENTITY + STATUS polling checks executable bytes, build provenance,
    // transport, protocol, closed schemas, and budget invariants, and readiness
    // is the lease taken on that checked connection. Retain the Child until
    // readiness or refusal so an early exit cannot be collapsed into the same
    // timeout as a slow but live process.
    spawn_until_adopted(
        &trustd,
        SPAWN_READY_TIMEOUT,
        LIVE_OWNER_ADOPT_TIMEOUT,
        || spawn_trustd(&trustd, sock),
        &mut owner_released,
        |deadline| lease_compatible_daemon_until(sock, &expected_identity, deadline),
    )
}

/// Spawn the packaged `trustd` for `sock`, its stderr captured (bounded) for
/// a refusal.
#[cfg(unix)]
fn spawn_trustd(
    trustd: &Path,
    sock: &Path,
) -> Result<(std::process::Child, thread::JoinHandle<String>), EnsureDaemonError> {
    // Spawn without inherited stdio. A tiny waiter thread owns the Child handle
    // so idle exit cannot leave a zombie in a long-lived launcher process.
    let mut command = std::process::Command::new(trustd);
    command
        .arg("--socket")
        .arg(sock)
        // The daemon is authenticated as exact packaged bytes. Inheriting a
        // loader-injection variable would let ambient code impersonate those
        // bytes after exec, so rebuild its tiny runtime environment from
        // constants owned by this client instead.
        .env_clear()
        .env("TRUST_MEMORY_JOBSERVER_DEADLINE_MS", acquire_deadline().as_millis().to_string())
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped());
    // Detach the daemon from its launcher's process group. trustd is the
    // machine-wide authority and outlives whoever happened to start it, but a
    // plain spawn leaves it in the launcher's group, and group-directed signals
    // are routine: Ctrl-C in a terminal, a CI step's teardown, and GNU
    // `timeout` (which moves itself and its child into a fresh group and
    // signals the WHOLE group on expiry). On 2026-09-22 exactly that — a
    // `timeout 150 ... targo trust check` probe — killed the production trustd
    // mid-epoch; it never recorded CLEAN, and every verified gate on the host
    // then refused to start until an operator ran `--recover-after-crash`.
    //
    // A new process group (not a new session) is sufficient and deliberate.
    // Terminal job-control signals (SIGINT/SIGQUIT/SIGTSTP) reach only the
    // terminal's foreground group; a shell's exit-time SIGHUP reaches only its
    // own jobs; the kernel's hangup SIGHUP on controlling-process exit reaches
    // only the foreground group; and the orphaned-group SIGHUP+SIGCONT fires
    // only for a group containing a STOPPED process, which trustd cannot
    // become (its stdio is never a terminal, and job-control stops are not
    // delivered to an orphaned group). None of those can name this group.
    // `setsid` would additionally drop the inherited controlling terminal, but
    // trustd never opens `/dev/tty`, and it would require an `unsafe`
    // `pre_exec` hook where this is a safe, posix_spawn-compatible attribute.
    {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }
    let mut child = command.spawn().map_err(|source| EnsureDaemonError::Spawn {
        executable: trustd.display().to_string(),
        source,
    })?;
    let stderr = child.stderr.take().expect("piped trustd stderr must be present");
    Ok((child, capture_spawned_stderr(stderr)))
}

/// Bounded liveness probe against an explicit trusted endpoint; `true` iff it
/// replies with exactly `PONG` before the observer deadline.
#[must_use]
#[cfg(unix)]
pub fn ping_at(sock: &Path) -> bool {
    ping_at_with_peer(sock, None)
}

#[cfg(unix)]
fn ping_at_with_peer(sock: &Path, expected_peer_pid: Option<u32>) -> bool {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let Ok(mut stream) = connect_trusted_until_with_pid(sock, deadline, expected_peer_pid) else {
        return false;
    };
    if write_line_until(&mut stream, "PING", deadline).is_err() {
        return false;
    }
    matches!(read_one_line_until(&stream, deadline), Some(l) if l.trim() == "PONG")
}

/// Exercise the complete diagnostic protocol against an endpoint that must
/// report the identity of `expected_executable`. Release evidence must use
/// [`exercise_daemon_at_from_pid`] to also authenticate the serving process.
///
/// The endpoint must begin empty, grant one real byte under `label`, expose the
/// matching active token, release it, and return to an empty state. Every I/O
/// operation uses the bounded client primitives above. This function never
/// spawns or discovers a daemon; the caller owns endpoint and child lifecycle.
#[cfg(unix)]
pub fn exercise_daemon_at(
    sock: &Path,
    expected_executable: &Path,
    label: &str,
) -> Result<DaemonSmoke, String> {
    let expected = daemon_identity_for_executable(expected_executable)
        .map_err(|error| format!("could not bind expected daemon executable: {error}"))?;
    exercise_daemon_at_with_identity(sock, expected_executable, &expected, label)
}

/// Release smoke variant that binds each protocol connection to a live,
/// unreaped direct child. Unsupported Unix hosts and unreadable credentials
/// refuse before sending any request on the affected connection.
#[cfg(unix)]
pub fn exercise_daemon_at_from_pid(
    sock: &Path,
    expected_executable: &Path,
    label: &str,
    spawned_child_pid: u32,
) -> Result<DaemonSmoke, String> {
    let expected = daemon_identity_for_executable(expected_executable)
        .map_err(|error| format!("could not bind expected daemon executable: {error}"))?;
    exercise_daemon_at_with_identity_and_peer(
        sock,
        expected_executable,
        &expected,
        label,
        Some(spawned_child_pid),
    )
}

/// Exercise the complete release-diagnostic protocol for an explicitly bound
/// candidate identity.
///
/// Unlike [`exercise_daemon_at`], this entry point does not assume the daemon
/// was built from the same release/commit as the client library. It hashes
/// `expected_executable` before the first and final identity checks, but the
/// protocol response remains self-report and does not bind the serving PID.
#[cfg(unix)]
pub fn exercise_daemon_at_with_identity(
    sock: &Path,
    expected_executable: &Path,
    expected: &DaemonIdentity,
    label: &str,
) -> Result<DaemonSmoke, String> {
    exercise_daemon_at_with_identity_and_peer(sock, expected_executable, expected, label, None)
}

#[cfg(unix)]
fn exercise_daemon_at_with_identity_and_peer(
    sock: &Path,
    expected_executable: &Path,
    expected: &DaemonIdentity,
    label: &str,
    expected_peer_pid: Option<u32>,
) -> Result<DaemonSmoke, String> {
    const SMOKE_BYTES: u64 = 1;

    if label.is_empty() || label.len() > MAX_LABEL_BYTES || label.contains(['\n', '\r']) {
        return Err(
            "daemon smoke label must be non-empty, single-line, and within the protocol bound"
                .to_string(),
        );
    }
    if !daemon_matches_bound_identity_with_peer(
        sock,
        expected_executable,
        expected,
        expected_peer_pid,
    ) {
        return Err("daemon endpoint does not match the exact expected executable".to_string());
    }
    if !ping_at_with_peer(sock, expected_peer_pid) {
        return Err("daemon did not answer PING with PONG".to_string());
    }
    let identity = identity_at_with_peer(sock, expected_peer_pid)
        .ok_or_else(|| "daemon did not return a valid closed IDENTITY response".to_string())?;
    let before = status_at_with_peer(sock, expected_peer_pid)
        .ok_or_else(|| "daemon did not return a valid initial STATUS response".to_string())?;
    if before.reserved_bytes != 0 || !before.active.is_empty() {
        return Err("daemon smoke requires an initially empty reservation state".to_string());
    }

    let reservation = reserve_via_daemon_with_peer(
        sock,
        SMOKE_BYTES,
        label,
        OBSERVER_IO_TIMEOUT,
        expected_peer_pid,
        machine_budget_bytes,
    )
    .map_err(|error| format!("daemon did not grant the smoke RESERVE request: {error}"))?;
    if !reservation.is_active() || reservation.bytes() != SMOKE_BYTES {
        return Err("daemon did not grant one active smoke reservation byte".to_string());
    }
    let reserved = status_at_with_peer(sock, expected_peer_pid)
        .ok_or_else(|| "daemon did not return the reserved STATUS response".to_string())?;
    let pid = std::process::id();
    let token = reserved.active.first().map(|active| active.token).unwrap_or_default();
    if !daemon_smoke_transition_is_valid(&before, &reserved, None, pid, token, label) {
        return Err("daemon reserved STATUS violated the smoke transition invariants".to_string());
    }

    release(reservation);
    let release_deadline =
        Instant::now().checked_add(Duration::from_secs(2)).unwrap_or_else(Instant::now);
    let released = loop {
        let status = status_at_with_peer(sock, expected_peer_pid)
            .ok_or_else(|| "daemon did not return the released STATUS response".to_string())?;
        if status.reserved_bytes == 0 && status.active.is_empty() {
            break status;
        }
        if Instant::now() >= release_deadline {
            return Err("daemon did not expose RELEASE within two seconds".to_string());
        }
        thread::sleep(Duration::from_millis(10));
    };
    if !daemon_smoke_transition_is_valid(&before, &reserved, Some(&released), pid, token, label) {
        return Err("daemon released STATUS violated the smoke transition invariants".to_string());
    }
    if !daemon_matches_bound_identity_with_peer(
        sock,
        expected_executable,
        expected,
        expected_peer_pid,
    ) {
        return Err("daemon identity changed during the smoke exchange".to_string());
    }

    Ok(DaemonSmoke {
        identity,
        status_before: before,
        status_reserved: reserved,
        status_released: released,
        reservation_pid: pid,
        reservation_token: token,
        reservation_bytes: SMOKE_BYTES,
        reservation_label: label.to_string(),
    })
}

#[cfg(unix)]
fn daemon_smoke_transition_is_valid(
    before: &DaemonStatus,
    reserved: &DaemonStatus,
    released: Option<&DaemonStatus>,
    pid: u32,
    token: u64,
    label: &str,
) -> bool {
    let reserved_valid = before.is_semantically_valid()
        && reserved.is_semantically_valid()
        && before.reserved_bytes == 0
        && before.active.is_empty()
        && before.budget_bytes > 0
        && token != 0
        && reserved.version == before.version
        && reserved.started_at == before.started_at
        && reserved.budget_bytes == before.budget_bytes
        && reserved.reserved_bytes == 1
        && reserved.free_bytes == before.free_bytes.saturating_sub(1)
        && reserved.granted_total == before.granted_total.saturating_add(1)
        && reserved.released_total == before.released_total
        && reserved.active.len() == 1
        && reserved.active[0].pid == pid
        && reserved.active[0].bytes == 1
        && reserved.active[0].label == label
        && reserved.active[0].token == token;
    let Some(released) = released else {
        return reserved_valid;
    };
    reserved_valid
        && released.is_semantically_valid()
        && released.version == before.version
        && released.started_at == before.started_at
        && released.budget_bytes == before.budget_bytes
        && released.reserved_bytes == 0
        && released.free_bytes == before.free_bytes
        && released.granted_total == reserved.granted_total
        && released.released_total == before.released_total.saturating_add(1)
        && released.active.is_empty()
}

/// Resolve the canonical `trustd` binary packaged beside the current executable.
/// Fail closed when it is absent, non-executable, or a symlink; never consult
/// `$CARGO_HOME` or `PATH` for an ambient authority.
#[cfg(unix)]
fn resolve_trustd() -> Result<(PathBuf, DaemonIdentity), EnsureDaemonError> {
    let current = std::env::current_exe()
        .map_err(|source| EnsureDaemonError::CurrentExecutable { source })?;
    let candidate = resolve_trustd_sibling(&current).ok_or_else(|| {
        EnsureDaemonError::SiblingUnavailable { executable: current.display().to_string() }
    })?;
    // Return the same canonical, full-ancestor-authorized path that identity
    // hashing consumes. `ensure_daemon` must never hash one pathname and exec a
    // second traversal through a replaceable symlink/ancestor.
    let path = canonical_trusted_executable_path(&candidate).map_err(|source| {
        EnsureDaemonError::ExecutableAuthority {
            executable: candidate.display().to_string(),
            source,
        }
    })?;
    let identity = daemon_identity_for_executable(&path).map_err(|source| {
        EnsureDaemonError::Identity { executable: path.display().to_string(), source }
    })?;
    Ok((path, identity))
}

/// Expected identity of the authorized same-sysroot executable, never read from
/// the server being authenticated. This is not executable/process attestation.
#[cfg(unix)]
pub fn expected_daemon_identity() -> Result<DaemonIdentity, EnsureDaemonError> {
    resolve_trustd().map(|(_, identity)| identity)
}

#[cfg(unix)]
fn resolve_trustd_sibling(executable: &Path) -> Option<PathBuf> {
    use std::os::unix::fs::PermissionsExt as _;

    let candidate = executable.parent()?.join(format!("trustd{}", std::env::consts::EXE_SUFFIX));
    let metadata = std::fs::symlink_metadata(&candidate).ok()?;
    if !metadata.file_type().is_file() || metadata.permissions().mode() & 0o111 == 0 {
        return None;
    }
    Some(candidate)
}

// ===========================================================================
// Helpers
// ===========================================================================

/// The configured socket path from [`SOCK_ENV`], if any. Presence selects the
/// daemon authority: an empty value is malformed configuration and must never
/// collapse into the unconfigured/inert lane.
fn sock_path() -> Result<Option<std::path::PathBuf>, String> {
    match std::env::var_os(SOCK_ENV) {
        Some(p) if !p.is_empty() => Ok(Some(std::path::PathBuf::from(p))),
        Some(_) => Err(format!("{SOCK_ENV} is configured with an empty path")),
        None => Ok(None),
    }
}

/// Whether the daemon path is force-disabled ([`DISABLE_ENV`] == "1").
fn disabled() -> bool {
    std::env::var(DISABLE_ENV).map(|v| v == "1").unwrap_or(false)
}

fn remaining_until(deadline: Instant) -> std::io::Result<Duration> {
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        Err(std::io::Error::new(std::io::ErrorKind::TimedOut, "trustd I/O deadline elapsed"))
    } else {
        Ok(remaining)
    }
}

#[cfg(unix)]
fn write_line_until(stream: &mut UnixStream, line: &str, deadline: Instant) -> std::io::Result<()> {
    let mut framed = Vec::with_capacity(line.len() + 1);
    framed.extend_from_slice(line.as_bytes());
    framed.push(b'\n');
    let mut written = 0usize;
    while written < framed.len() {
        let remaining = remaining_until(deadline)?;
        let timeout_ms = remaining.as_millis().max(1).min(i32::MAX as u128) as i32;
        let mut poll_fd =
            libc::pollfd { fd: stream.as_raw_fd(), events: libc::POLLOUT, revents: 0 };
        let polled = unsafe { libc::poll(&mut poll_fd, 1, timeout_ms) };
        if polled < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if polled == 0 {
            continue;
        }
        if Instant::now() >= deadline {
            return Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "trustd I/O deadline elapsed",
            ));
        }
        if poll_fd.revents & libc::POLLNVAL != 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "trustd socket descriptor became invalid",
            ));
        }
        let sent = unsafe {
            libc::send(
                stream.as_raw_fd(),
                framed[written..].as_ptr().cast::<libc::c_void>(),
                framed.len() - written,
                libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL,
            )
        };
        if sent < 0 {
            let error = std::io::Error::last_os_error();
            if matches!(
                error.kind(),
                std::io::ErrorKind::Interrupted | std::io::ErrorKind::WouldBlock
            ) {
                continue;
            }
            return Err(error);
        }
        if sent == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::WriteZero,
                "trustd socket accepted zero request bytes",
            ));
        }
        written += sent as usize;
    }
    Ok(())
}

/// Read exactly one newline-terminated line from `stream` under one absolute
/// deadline. EOF before newline, invalid UTF-8, and oversized replies fail
/// closed. Polling before each direct byte read enforces the absolute deadline
/// without repeatedly mutating `SO_RCVTIMEO`; Darwin can reject a second
/// sub-second timeout update after the first read even while reply bytes remain.
#[cfg(unix)]
fn read_one_line_until(stream: &UnixStream, deadline: Instant) -> Option<String> {
    read_one_line_until_limited(stream, deadline, MAX_REQUEST_BYTES * 64)
}

#[cfg(unix)]
fn read_one_line_until_limited(
    stream: &UnixStream,
    deadline: Instant,
    limit: usize,
) -> Option<String> {
    let mut reader = stream.try_clone().ok()?;
    let mut buf: Vec<u8> = Vec::with_capacity(128);
    let mut byte = [0u8; 1];
    loop {
        let remaining = remaining_until(deadline).ok()?;
        let timeout_ms = remaining.as_millis().max(1).min(i32::MAX as u128) as i32;
        let mut poll_fd = libc::pollfd { fd: reader.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        let polled = unsafe { libc::poll(&mut poll_fd, 1, timeout_ms) };
        if polled < 0 {
            if std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return None;
        }
        if polled == 0 {
            continue;
        }
        if Instant::now() >= deadline || poll_fd.revents & libc::POLLNVAL != 0 {
            return None;
        }
        match reader.read(&mut byte) {
            Ok(0) => return None,
            Ok(_) => {
                if byte[0] == b'\n' {
                    return String::from_utf8(buf).ok();
                }
                // STATUS JSON can be larger than a request; allow a generous cap.
                if buf.len() >= limit {
                    return None;
                }
                buf.push(byte[0]);
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(_) => return None,
        }
    }
}

#[cfg(all(unix, test))]
fn read_one_line(stream: &UnixStream) -> Option<String> {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    read_one_line_until(stream, deadline)
}

fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

// ===========================================================================
// Tests (bounded; protocol over a temp UnixListener). NOT run in this phase
// (cargo test is the OOM path) — they compile under `cargo check`.
// ===========================================================================
#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

    use super::*;

    /// Stop and reap an owned child even when an assertion unwinds the test.
    struct TestChild(std::process::Child);

    impl Drop for TestChild {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }

    struct TestSocket {
        path: std::path::PathBuf,
    }

    impl TestSocket {
        fn new(label: &str) -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            // macOS resolves its per-session temporary directory through a
            // long `/private/var/folders/...` prefix. The production binder's
            // deliberately private staging component can then exceed AF_UNIX's
            // small pathname limit even though the behavior under test is not
            // path-length handling. `/tmp` is the daemon's real stable runtime
            // namespace and canonicalizes to a short, trusted sticky directory.
            let temp_root =
                std::fs::canonicalize("/tmp").expect("canonical system temporary directory");
            for _ in 0..128 {
                let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
                let root =
                    temp_root.join(format!("trustd-{label}-{}-{sequence}", std::process::id()));
                let mut builder = std::fs::DirBuilder::new();
                builder.mode(0o700);
                match builder.create(&root) {
                    Ok(()) => {
                        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700))
                            .expect("make test socket directory private");
                        return Self { path: root.join("daemon.sock") };
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("create test socket directory: {error}"),
                }
            }
            panic!("could not allocate a unique test socket directory")
        }

        fn lock_path(&self) -> std::path::PathBuf {
            let mut lock = self.path.as_os_str().to_owned();
            lock.push(".lock");
            std::path::PathBuf::from(lock)
        }
    }

    impl Drop for TestSocket {
        fn drop(&mut self) {
            // Test socket paths are unique, so a sentinel can be removed after
            // acquiring its kernel lock. If a panicking test still has a live
            // owner, acquisition fails and preserving the sentinel is safer
            // than splitting that ownership domain.
            if let Ok(canonical) = canonical_socket_path(&self.path) {
                if let Ok((ownership, _)) = open_stable_ownership_lock(&canonical) {
                    let _ = std::fs::remove_file(&ownership.path);
                }
            }
            let _ = std::fs::remove_file(&self.path);
            let _ = std::fs::remove_file(self.lock_path());
            if let Some(parent) = self.path.parent() {
                let _ = std::fs::remove_dir(parent);
            }
        }
    }

    /// A daemon with a fixed test budget, bypassing `machine_budget_bytes`, so
    /// admission logic is exercised deterministically without touching RAM.
    fn test_daemon(budget: u64) -> Arc<Daemon> {
        Daemon::with_budget(budget)
    }

    /// The observational deadline a *protocol* test hands the client, in place
    /// of the production `OBSERVER_IO_TIMEOUT`.
    ///
    /// A test that spawns its own responder and then immediately starts an
    /// absolute 500 ms client clock is not measuring the wire protocol: it is
    /// measuring whether a loaded host scheduled that responder in time. The
    /// production bound is deliberate policy and keeps its own dedicated
    /// coverage in `bounded_client_read_rejects_a_trickled_frame_past_its_
    /// absolute_deadline`, which drives the clock against a responder whose
    /// slowness is the thing under test.
    const TEST_OBSERVER_TIMEOUT: Duration = Duration::from_secs(30);

    /// A fixed client budget for tests that pin *both* sides of
    /// `daemon_budget_is_acceptable`. Reading `machine_budget_bytes()` instead
    /// would enroll the test in the process-global `BUDGET_BYTES_CACHE`, which
    /// a concurrently running sibling can rewrite between the daemon's
    /// advertised ceiling and the client's acceptance check — refusing a
    /// perfectly valid daemon. Two constants cannot race.
    const TEST_CLIENT_BUDGET: u64 = 1 << 30;

    /// Spawn a socket responder and return only once its thread has provably
    /// been scheduled and entered `body`. The listener is bound and listening
    /// before the spawn, so from here on the client is talking to a live
    /// responder rather than to one the kernel has not run yet — the client's
    /// deadline measures the protocol, not thread start-up latency.
    fn spawn_ready_responder<F>(body: F) -> thread::JoinHandle<()>
    where
        F: FnOnce() + Send + 'static,
    {
        let ready = Arc::new(std::sync::Barrier::new(2));
        let signal = Arc::clone(&ready);
        let handle = thread::spawn(move || {
            signal.wait();
            body();
        });
        ready.wait();
        handle
    }

    fn make_socket_private(path: &Path) {
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
            .expect("make test socket private");
    }

    fn synthetic_protocol_pid() -> u32 {
        // The wire grammar admits positive signed-PID values, but the daemon
        // deliberately treats them as diagnostics rather than lifetime
        // authority because PID numbers differ across namespaces.
        i32::MAX as u32
    }

    struct ScopedEnvOverride {
        name: &'static str,
        previous: Option<std::ffi::OsString>,
    }

    impl ScopedEnvOverride {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn set(name: &'static str, value: impl AsRef<std::ffi::OsStr>) -> Self {
            let previous = std::env::var_os(name);
            unsafe { std::env::set_var(name, value) };
            Self { name, previous }
        }

        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn remove(name: &'static str) -> Self {
            let previous = std::env::var_os(name);
            unsafe { std::env::remove_var(name) };
            Self { name, previous }
        }
    }

    impl Drop for ScopedEnvOverride {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn drop(&mut self) {
            match &self.previous {
                Some(value) => unsafe { std::env::set_var(self.name, value) },
                None => unsafe { std::env::remove_var(self.name) },
            }
        }
    }

    struct TestFileLane {
        path: PathBuf,
        directory: PathBuf,
    }

    impl TestFileLane {
        fn new(label: &str) -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
            // Root under $HOME, NOT the checkout — the same correction Part A
            // made to `memory_jobserver::TestDirectory`, for the same reason.
            //
            // The comment this replaced said to "place this fixture below the
            // checkout, whose euid/root-owned chain matches the accepted
            // production shape". That is false under the common `umask 0002`:
            // every directory in a checked-out repo is 0775, and the ledger
            // rejects a token whose ANCESTOR chain is group/other writable. The
            // leaf is 0700 (set below) and everything above it is not, which is
            // why the failure reads as puzzling — "token ancestor is
            // group/other writable: .../crates/trust-router". `/tmp` is no
            // better: it is 1777, and this check has no root-owned-sticky
            // exemption. `$HOME` is 0750 owner-only on a normal account.
            //
            // Falls back to the temp dir when HOME is unset (CI containers),
            // which reproduces the old failure loudly rather than skipping.
            let base = std::env::var_os("HOME")
                .map(PathBuf::from)
                .unwrap_or_else(std::env::temp_dir)
                .join(".cache")
                .join("trust-file-lane-tests");
            std::fs::create_dir_all(&base).expect("create file-lane test root");
            std::fs::set_permissions(&base, std::fs::Permissions::from_mode(0o700))
                .expect("make file-lane test root private");
            let directory =
                base.join(format!("{label}-{}-{nonce:x}-{sequence}", std::process::id()));
            std::fs::create_dir(&directory).expect("create private file-lane fixture");
            std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))
                .expect("make file-lane fixture private");
            let lane = Self { path: directory.join("fallback.tokens"), directory };
            lane.remove_artifacts();
            memory_jobserver::set_test_token_path(Some(lane.path.clone()));
            lane
        }

        fn lock_path(&self) -> PathBuf {
            let mut lock = self.path.as_os_str().to_owned();
            lock.push(".lock");
            PathBuf::from(lock)
        }

        fn remove_artifacts(&self) {
            let _ = std::fs::remove_file(&self.path);
            let _ = std::fs::remove_file(self.path.with_extension("tmp"));
            let _ = std::fs::remove_file(self.lock_path());
        }

        fn prove_lane_would_grant_then_reset(&self, bytes: u64) {
            let probe = memory_jobserver::acquire(bytes).expect("control file lane admission");
            assert!(probe.is_active(), "file-lane fixture must be capable of granting");
            drop(probe);
            assert!(self.path.exists(), "the control acquire minted the file ledger");
            std::fs::remove_file(&self.path).expect("reset control token ledger");
        }

        fn assert_no_token_minted(&self) {
            assert!(
                !self.path.exists(),
                "a selected daemon failure must not mint an independent file token"
            );
        }
    }

    impl Drop for TestFileLane {
        fn drop(&mut self) {
            memory_jobserver::set_test_token_path(None);
            self.remove_artifacts();
            let _ = std::fs::remove_dir(&self.directory);
        }
    }

    #[test]
    fn ping_replies_pong() {
        let d = test_daemon(1 << 30);
        assert_eq!(d.handle_line("PING"), "PONG");
        assert_eq!(d.handle_line("ping"), "PONG");
    }

    /// Endpoint loss must not wait for the idle timer: an empty ledger is the
    /// whole precondition, exactly as for idle shutdown, and activity age is
    /// irrelevant — the daemon has just been made unreachable.
    #[test]
    fn shutdown_if_unreserved_ignores_the_idle_timer() {
        let d = test_daemon(1 << 30);
        d.touch_activity();
        assert!(!d.idle_expired(), "fixture is freshly active");
        assert!(d.try_begin_shutdown_if_unreserved(), "empty ledger closes admission at once");
        assert!(d.shutting_down.load(AtomicOrdering::Acquire));
        assert!(d.try_begin_shutdown_if_unreserved(), "closing admission is idempotent");
    }

    #[test]
    fn identity_is_closed_and_observational() {
        let d = test_daemon(1 << 30);
        {
            let mut activity = d.last_activity.lock().unwrap_or_else(|error| error.into_inner());
            *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
        }
        let line = d.handle_line("IDENTITY");
        let parsed: DaemonIdentity = serde_json::from_str(&line).expect("valid identity JSON");
        assert!(parsed.has_valid_invariants());
        assert_eq!(parsed.protocol, STATUS_VERSION);
        assert!(d.idle_expired(), "IDENTITY must not refresh daemon activity");
        assert_eq!(d.handle_line("IDENTITY trailing"), "ERR bad-args");

        let mut value = serde_json::to_value(parsed).expect("serialize identity");
        value
            .as_object_mut()
            .expect("identity object")
            .insert("future".to_string(), serde_json::Value::Bool(true));
        assert!(
            serde_json::from_value::<DaemonIdentity>(value).is_err(),
            "closed identity schema rejects unknown fields"
        );
    }

    #[test]
    fn reserve_grants_then_release_frees() {
        let d = test_daemon(1 << 30); // 1 GiB
        let reply = d.handle_line("RESERVE 1048576 4321 mycrate");
        let token: u64 = reply.strip_prefix("GRANTED ").expect("granted").parse().expect("u64");
        assert!(token >= 1, "real grant gets a nonzero token");
        {
            let st = d.lock();
            assert_eq!(st.reserved_bytes, 1048576);
            assert_eq!(st.granted_total, 1);
            assert_eq!(st.active.len(), 1);
            assert_eq!(st.active[0].label, "mycrate");
        }
        assert_eq!(d.handle_line(&format!("RELEASE {token}")), "OK");
        {
            let st = d.lock();
            assert_eq!(st.reserved_bytes, 0);
            assert_eq!(st.released_total, 1);
            assert!(st.active.is_empty());
        }
    }

    #[test]
    fn zero_byte_reserve_is_sentinel() {
        let d = test_daemon(1 << 30);
        assert_eq!(d.handle_line("RESERVE 0 4321 x"), "GRANTED 0");
        // Sentinel grant is not counted and reserves nothing.
        let st = d.lock();
        assert_eq!(st.granted_total, 0);
        assert_eq!(st.reserved_bytes, 0);
    }

    #[test]
    fn release_unknown_token_is_ok() {
        let d = test_daemon(1 << 30);
        assert_eq!(d.handle_line("RELEASE 999999"), "OK");
        assert_eq!(d.handle_line("RELEASE 0"), "OK");
    }

    #[test]
    fn only_the_reserving_process_may_send_drop_release_after_fork() {
        let owner = std::process::id();
        assert!(reservation_owner_may_release(owner));
        assert!(
            !reservation_owner_may_release(owner.saturating_add(1)),
            "a forked copy must retain conservatively instead of releasing its parent's grant"
        );
    }

    #[test]
    fn impossible_request_degrades_immediately() {
        let d = test_daemon(1 << 20); // 1 MiB budget
        // Larger than the whole budget ⇒ DEGRADED without parking.
        assert_eq!(d.handle_line("RESERVE 1073741824 4321 big"), "DEGRADED");
    }

    #[test]
    fn zero_budget_degrades() {
        let d = test_daemon(0);
        assert_eq!(d.handle_line("RESERVE 1024 4321 x"), "DEGRADED");
    }

    #[test]
    fn production_budget_only_lowers_and_overcommit_blocks_new_grants() {
        let identity = test_daemon(1).identity.clone();
        let d = Daemon::with_budget_policy(8192, identity, BudgetPolicy::DynamicMachine);
        let pid = std::process::id();
        let token = 1;
        {
            // Seed a grant without consulting ambient machine state; this test
            // targets the transition after a production observation changes.
            let mut st = d.lock();
            st.active.push(ServerReservation {
                token,
                pid,
                bytes: 4096,
                label: "already-running".to_string(),
                granted_at: Instant::now(),
                work: None,
            });
            st.reserved_bytes = 4096;
            st.granted_total = 1;
            st.next_token = 2;
        }

        assert!(d.lower_dynamic_budget(2048));
        assert!(!d.lower_dynamic_budget(16384), "a later larger observation cannot raise it");
        let status: DaemonStatus =
            serde_json::from_str(&d.status_line()).expect("overcommitted STATUS JSON");
        assert_eq!(status.budget_bytes, 2048);
        assert_eq!(status.reserved_bytes, 4096);
        assert_eq!(status.free_bytes, 0);
        assert!(status.has_valid_invariants());
        assert_eq!(
            d.handle_line(&format!("RESERVE 4096 {pid} after-lowering")),
            "DEGRADED",
            "a request larger than the lowered ceiling fails immediately"
        );
        assert_eq!(d.handle_line(&format!("RELEASE {token}")), "OK");

        let fixed = test_daemon(8192);
        assert!(!fixed.lower_dynamic_budget(1024));
        assert_eq!(fixed.lock().budget_bytes, 8192, "fixed tests ignore ambient refresh");
    }

    #[test]
    fn over_budget_blocks_then_degrades() {
        // Force a short deadline so the parked RESERVE returns DEGRADED quickly.
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _deadline = ScopedEnvOverride::set("TRUST_MEMORY_JOBSERVER_DEADLINE_MS", "100");
        let d = test_daemon(1 << 20); // 1 MiB
        // Reserve the whole budget. Client-reported PIDs are diagnostic only;
        // this direct state-machine test releases its token explicitly below.
        let pid = std::process::id();
        let r = d.handle_line(&format!("RESERVE 1048576 {pid} hog"));
        assert!(r.starts_with("GRANTED "));
        // A second request that fits alone but not now must block ~deadline then
        // degrade (never hang).
        let t0 = Instant::now();
        let blocked = d.handle_line(&format!("RESERVE 524288 {pid} waiter"));
        let waited = t0.elapsed();
        assert_eq!(blocked, "DEGRADED");
        assert!(waited >= Duration::from_millis(80), "must block, waited {waited:?}");
    }

    #[test]
    fn release_admits_a_parked_waiter() {
        // A long deadline so the waiter parks (does not time out) while a peer
        // releases; the waiter must then be admitted.
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _deadline = ScopedEnvOverride::set("TRUST_MEMORY_JOBSERVER_DEADLINE_MS", "5000");
        let d = test_daemon(1 << 20); // 1 MiB
        let first = d.handle_line("RESERVE 1048576 4321 hog");
        let token: u64 = first.strip_prefix("GRANTED ").expect("granted").parse().expect("u64");
        // Park a waiter for the remaining budget in a thread.
        let d2 = Arc::clone(&d);
        let waiter = thread::spawn(move || d2.handle_line("RESERVE 524288 4322 waiter"));
        // Give the waiter a moment to park, then release the hog.
        thread::sleep(Duration::from_millis(100));
        assert_eq!(d.handle_line(&format!("RELEASE {token}")), "OK");
        let admitted = waiter.join().expect("waiter joined");
        assert!(
            admitted.starts_with("GRANTED "),
            "released budget admits the parked waiter: {admitted}"
        );
    }

    #[test]
    fn status_round_trips_json() {
        let d = test_daemon(8 << 30);
        // Use the live test-runner pid so the background admission semantics and
        // the snapshot both describe a genuinely active worker.
        let pid = std::process::id();
        let _ = d.handle_line(&format!("RESERVE 4096 {pid} alpha"));
        let line = d.handle_line("STATUS");
        let parsed: DaemonStatus = serde_json::from_str(&line).expect("valid status json");
        assert_eq!(parsed.version, STATUS_VERSION);
        assert_eq!(parsed.budget_bytes, 8 << 30);
        assert_eq!(parsed.reserved_bytes, 4096);
        assert_eq!(parsed.free_bytes, (8u64 << 30) - 4096);
        assert_eq!(parsed.active.len(), 1);
        assert_eq!(parsed.active[0].label, "alpha");
        assert_eq!(parsed.active[0].pid, pid);
        assert!(parsed.has_valid_invariants());
        assert!(parsed.is_semantically_valid());
    }

    #[test]
    fn status_rejects_unknown_fields_wrong_version_and_broken_invariants() {
        let mut status = DaemonStatus {
            version: STATUS_VERSION.to_string(),
            budget_bytes: 8192,
            reserved_bytes: 4096,
            free_bytes: 4096,
            queue_depth: 0,
            granted_total: 1,
            released_total: 0,
            started_at: unix_now(),
            active: vec![ActiveReservation {
                pid: std::process::id(),
                bytes: 4096,
                label: "alpha".to_string(),
                since_secs: 0,
                token: 1,
            }],
        };
        assert!(status.has_valid_invariants());

        status.version = "trustd.status.v2".to_string();
        assert!(!status.has_valid_invariants());
        status.version = STATUS_VERSION.to_string();
        status.free_bytes = 1;
        assert!(!status.has_valid_invariants());
        status.free_bytes = 4096;
        status.active[0].bytes = 2048;
        assert!(!status.has_valid_invariants());
        status.active[0].bytes = 4096;
        status.released_total = 1;
        assert!(!status.has_valid_invariants());
        status.released_total = 0;

        // A lowered runtime ceiling can temporarily sit below live grants. The
        // safe representation keeps every byte accounted and advertises zero
        // free capacity.
        status.budget_bytes = 2048;
        status.free_bytes = 0;
        assert!(status.has_valid_invariants());
        status.free_bytes = 1;
        assert!(!status.has_valid_invariants());

        let mut json = serde_json::to_value(&status).expect("serialize status");
        json.as_object_mut()
            .expect("status object")
            .insert("future_field".to_string(), serde_json::json!(true));
        assert!(
            serde_json::from_value::<DaemonStatus>(json).is_err(),
            "closed v1 schema must reject unknown fields"
        );
    }

    #[test]
    fn status_at_rejects_semantically_invalid_wire_response() {
        let fixture = TestSocket::new("invalid-status");
        let listener = UnixListener::bind(&fixture.path).expect("bind invalid status server");
        make_socket_private(&fixture.path);
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("accept status client");
            writeln!(
                stream,
                "{{\"version\":\"{STATUS_VERSION}\",\"budget_bytes\":10,\"reserved_bytes\":9,\"free_bytes\":9,\"queue_depth\":0,\"granted_total\":0,\"released_total\":0,\"started_at\":0,\"active\":[]}}"
            )
            .expect("write invalid status");
        });
        assert!(status_at(&fixture.path).is_none());
        server.join().expect("invalid status server joined");
    }

    #[test]
    fn bounded_client_read_accepts_a_complete_multibyte_frame() {
        let (client, mut server) = UnixStream::pair().expect("create client I/O pair");
        server.write_all(b"complete-multibyte-frame\n").expect("write complete frame");
        let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
        assert_eq!(
            read_one_line_until(&client, deadline).as_deref(),
            Some("complete-multibyte-frame")
        );
    }

    #[test]
    fn bounded_client_read_rejects_a_trickled_frame_past_its_absolute_deadline() {
        let (client, mut server) = UnixStream::pair().expect("create trickle I/O pair");
        server.write_all(b"x").expect("write first trickle byte");
        let writer = thread::spawn(move || {
            thread::sleep(Duration::from_millis(100));
            let _ = server.write_all(b"\n");
        });
        let started = Instant::now();
        let deadline = started.checked_add(Duration::from_millis(40)).unwrap_or(started);
        assert!(read_one_line_until(&client, deadline).is_none());
        assert!(
            started.elapsed() < Duration::from_millis(250),
            "trickled response exceeded the bounded client deadline"
        );
        writer.join().expect("trickle writer joined");
    }

    #[test]
    fn bounded_client_write_supports_multiple_frames_on_one_connection() {
        let (mut client, mut server) = UnixStream::pair().expect("create writer I/O pair");
        let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
        write_line_until(&mut client, "IDENTITY", deadline).expect("write first bounded frame");
        write_line_until(&mut client, "STATUS", deadline).expect("write second bounded frame");
        drop(client);
        let mut bytes = Vec::new();
        server.read_to_end(&mut bytes).expect("read bounded frames");
        assert_eq!(bytes, b"IDENTITY\nSTATUS\n");
    }

    #[test]
    fn compatible_status_endpoint_with_wrong_binary_identity_is_rejected() {
        let fixture = TestSocket::new("wrong-identity");
        let listener = UnixListener::bind(&fixture.path).expect("bind wrong identity server");
        make_socket_private(&fixture.path);
        let actual = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: compiled_release().to_string(),
            commit: compiled_commit().to_string(),
            executable_sha256: "a".repeat(64),
        };
        let mut expected = actual.clone();
        expected.executable_sha256 = "b".repeat(64);
        let daemon = Daemon::with_budget_and_identity(1 << 30, actual);
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept identity client");
            daemon.serve_conn(stream);
        });

        assert!(
            lease_compatible_daemon_at(&fixture.path, &expected).is_none(),
            "STATUS v1 compatibility cannot override a mismatched executable hash"
        );
        server.join().expect("wrong identity server joined");
    }

    #[test]
    fn explicit_cross_version_identity_still_binds_exact_executable_bytes() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Supply the machine total, as this test already supplies a socket and a
        // token path. Without it `machine_budget_bytes()` is 0 wherever the visible
        // cgroup root has no `memory.max` (every bare-metal cgroup-v2 Linux box), and
        // the admission this test exists to exercise is refused before it begins.
        // NOT the fail-closed cgroup exemption — that rule governs production.
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("explicit-cross-version-identity");
        let executable = fixture.path.parent().expect("fixture parent").join("trustd");
        std::fs::write(&executable, b"cross-version packaged trustd").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700))
            .expect("make executable private");
        let identity = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: "9.99.0-candidate".to_string(),
            commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
            executable_sha256: executable_sha256(&executable).expect("hash executable"),
        };
        let listener = UnixListener::bind(&fixture.path).expect("bind cross-version daemon");
        make_socket_private(&fixture.path);
        let daemon = Daemon::with_budget_and_identity(1, identity.clone());
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept cross-version client");
            daemon.serve_conn(stream);
        });

        let mut asserted = identity.clone();
        asserted.executable_sha256 = "0".repeat(64);
        assert!(
            !daemon_matches_bound_identity(&fixture.path, &executable, &asserted),
            "an asserted cross-version digest must not replace independent byte hashing"
        );
        assert!(
            daemon_matches_bound_identity(&fixture.path, &executable, &identity),
            "an explicitly supplied candidate identity should permit a cross-version probe"
        );
        server.join().expect("cross-version server joined");

        std::fs::remove_file(executable).expect("remove executable fixture");
    }

    #[test]
    fn retained_client_build_preserves_default_and_executable_authority() {
        let original = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: "0.13.0".to_string(),
            commit: "1".repeat(40),
            executable_sha256: "a".repeat(64),
        };
        assert_eq!(client_build_identity(original.clone(), None).unwrap(), original);
        let selected = client_build_identity(
            original.clone(),
            Some(("1.101.0-dev", "2222222222222222222222222222222222222222")),
        )
        .unwrap();
        assert_eq!(selected.release, "1.101.0-dev");
        assert_eq!(selected.commit, "2".repeat(40));
        assert_eq!(selected.version, original.version);
        assert_eq!(selected.protocol, original.protocol);
        assert_eq!(selected.executable_sha256, original.executable_sha256);
        for (release, commit) in [
            ("", "2222222222222222222222222222222222222222"),
            ("1.101.0-dev\n", "2222222222222222222222222222222222222222"),
            ("1.101.0-dev", "short"),
            ("1.101.0-dev", "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
        ] {
            assert!(client_build_identity(original.clone(), Some((release, commit))).is_err());
        }
    }

    #[test]
    fn retained_client_build_adopts_only_the_bound_daemon_identity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("retained-client-build");
        let executable = fixture.path.parent().expect("fixture parent").join("trustd");
        std::fs::write(&executable, b"retained packaged trustd fixture").unwrap();
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700)).unwrap();
        let original = daemon_identity_for_executable(&executable).unwrap();
        let target =
            if original.commit == "2".repeat(40) { "1".repeat(40) } else { "2".repeat(40) };
        let selected =
            client_build_identity(original.clone(), Some(("1.101.0-dev", &target))).unwrap();
        let listener = UnixListener::bind(&fixture.path).unwrap();
        make_socket_private(&fixture.path);
        // The injected total is reduced by the ordinary client budget policy;
        // serve that same ceiling so this test isolates identity admission.
        let daemon = Daemon::with_budget_and_identity(machine_budget_bytes(), selected.clone());
        let mut wrong_digest = selected.clone();
        wrong_digest.executable_sha256 = "0".repeat(64);
        for (expected, accepted) in [(original, false), (wrong_digest, false), (selected, true)] {
            let serving = Arc::clone(&daemon);
            let listener = listener.try_clone().unwrap();
            let server = thread::spawn(move || {
                let (stream, _) = listener.accept().unwrap();
                serving.serve_conn(stream);
            });
            let lease = lease_compatible_daemon_at(&fixture.path, &expected);
            assert_eq!(lease.is_some(), accepted);
            drop(lease);
            server.join().unwrap();
        }
        std::fs::remove_file(executable).expect("remove retained executable fixture");
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn matching_fake_daemon_cannot_impersonate_live_spawned_child() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("peer-pid-mismatch");
        let executable = fixture.path.parent().expect("fixture parent").join("trustd");
        std::fs::write(&executable, b"candidate trustd fixture").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700))
            .expect("make executable private");
        let identity = daemon_identity_for_executable(&executable).expect("bind fixture identity");
        let listener = UnixListener::bind(&fixture.path).expect("bind fake daemon");
        listener.set_nonblocking(true).expect("bound fake daemon listener");
        make_socket_private(&fixture.path);
        let daemon = Daemon::with_budget_and_identity(1, identity);
        let stop = Arc::new(AtomicBool::new(false));
        let server_stop = Arc::clone(&stop);
        let server = spawn_ready_responder(move || {
            while !server_stop.load(AtomicOrdering::Relaxed) {
                match listener.accept() {
                    Ok((stream, _)) => daemon.serve_conn(stream),
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("accept fake daemon client: {error}"),
                }
            }
        });

        let mut other_child = std::process::Command::new("/bin/cat")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("spawn live unrelated child");
        assert!(require_live_unreaped_child(other_child.id()).is_ok());
        assert!(daemon_matches_executable(&fixture.path, &executable));
        assert!(
            !daemon_matches_executable_from_pid(&fixture.path, &executable, other_child.id()),
            "a live child PID must not substitute for the socket peer PID"
        );
        assert!(
            exercise_daemon_at_from_pid(&fixture.path, &executable, "smoke", other_child.id())
                .is_err(),
            "smoke must refuse a live child that does not serve the socket"
        );
        assert!(
            !daemon_matches_executable_from_pid(&fixture.path, &executable, std::process::id()),
            "the serving process is not its own spawned child"
        );
        assert!(
            exercise_daemon_at_from_pid(&fixture.path, &executable, "smoke", std::process::id())
                .is_err(),
            "peer-matching self PID must not fabricate a child-bound release smoke"
        );
        stop.store(true, AtomicOrdering::Relaxed);
        server.join().expect("fake daemon server joined");
        other_child.kill().expect("stop unrelated child");
        let exit_deadline = Instant::now() + Duration::from_secs(2);
        loop {
            match require_live_unreaped_child(other_child.id()) {
                Err(error) if error.kind() == std::io::ErrorKind::BrokenPipe => break,
                Ok(()) if Instant::now() < exit_deadline => {
                    thread::sleep(Duration::from_millis(5));
                }
                result => panic!("unreaped child must report exit: {result:?}"),
            }
        }
        other_child.wait().expect("reap unrelated child");
        std::fs::remove_file(executable).expect("remove executable fixture");
    }

    #[test]
    fn same_euid_client_rejects_daemon_from_a_broader_cgroup_budget() {
        let fixture = TestSocket::new("broader-cgroup");
        let listener = UnixListener::bind(&fixture.path).expect("bind broader daemon");
        make_socket_private(&fixture.path);
        let identity = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: compiled_release().to_string(),
            commit: compiled_commit().to_string(),
            executable_sha256: "c".repeat(64),
        };
        let daemon = Daemon::with_budget_and_identity(4096, identity.clone());
        let server = thread::spawn(move || {
            for stream in listener.incoming().take(2) {
                daemon.serve_conn(stream.expect("accept compatibility client"));
            }
        });

        let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
        let narrower = lease_compatible_daemon_until_with_budget_source(
            &fixture.path,
            &identity,
            deadline,
            || 1024,
        );
        assert!(narrower.is_none(), "a narrower client must not adopt a broader daemon ceiling");
        let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
        let equal = lease_compatible_daemon_until_with_budget_source(
            &fixture.path,
            &identity,
            deadline,
            || 4096,
        );
        assert!(equal.is_some(), "an equal client budget may adopt the exact daemon");
        // The adopted daemon's handler serves its lease until EOF.
        drop(equal);
        server.join().expect("broader-cgroup server joined");
    }

    #[test]
    fn configured_hung_daemon_fails_without_minting_file_capacity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Supply the machine total, as this test already supplies a socket and a
        // token path. Without it `machine_budget_bytes()` is 0 wherever the visible
        // cgroup root has no `memory.max` (every bare-metal cgroup-v2 Linux box), and
        // the admission this test exists to exercise is refused before it begins.
        // NOT the fail-closed cgroup exemption — that rule governs production.
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("hung-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind hung responder");
        make_socket_private(&fixture.path);
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let _deadline = ScopedEnvOverride::set("TRUST_MEMORY_JOBSERVER_DEADLINE_MS", "50");
        let file_lane = TestFileLane::new("hung");
        file_lane.prove_lane_would_grant_then_reset(4096);

        let status = test_daemon(machine_budget_bytes()).status_line();
        let (stop_tx, stop_rx) = std::sync::mpsc::channel();
        // This test DOES assert the production deadline — that is its purpose —
        // so the responder must be provably running before the clock starts,
        // or the window below measures thread start-up as well.
        let server = spawn_ready_responder(move || {
            let (mut stream, _) = listener.accept().expect("accept reserve client");
            assert_eq!(read_one_line(&stream).as_deref(), Some("STATUS"));
            writeln!(stream, "{status}").expect("write valid STATUS preflight");
            stream.flush().expect("flush valid STATUS preflight");
            assert!(
                read_one_line(&stream).is_some_and(|request| request.starts_with("RESERVE ")),
                "client reaches the deliberately hung reservation phase"
            );
            let _ = stop_rx.recv();
        });

        let started = Instant::now();
        let error = reserve_labeled(4096, "hung")
            .expect_err("a hung selected daemon must block solver launch");
        let elapsed = started.elapsed();
        assert!(
            error.to_string().contains("did not return one complete reply"),
            "unexpected configured-daemon failure: {error}"
        );
        file_lane.assert_no_token_minted();
        assert!(
            elapsed < Duration::from_secs(1),
            "hung responder exceeded admission deadline plus margin: {elapsed:?}"
        );

        stop_tx.send(()).expect("release hung responder");
        server.join().expect("hung responder joined");
    }

    #[test]
    fn configured_malformed_daemon_fails_without_minting_file_capacity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Supply the machine total, as this test already supplies a socket and a
        // token path. Without it `machine_budget_bytes()` is 0 wherever the visible
        // cgroup root has no `memory.max` (every bare-metal cgroup-v2 Linux box), and
        // the admission this test exists to exercise is refused before it begins.
        // NOT the fail-closed cgroup exemption — that rule governs production.
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("malformed-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind malformed responder");
        make_socket_private(&fixture.path);
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let file_lane = TestFileLane::new("malformed");
        file_lane.prove_lane_would_grant_then_reset(4096);

        let (stop_tx, stop_rx) = std::sync::mpsc::channel();
        let server = spawn_ready_responder(move || {
            let (mut stream, _) = listener.accept().expect("accept reserve client");
            let request = read_one_line(&stream).expect("read STATUS frame");
            assert_eq!(request, "STATUS");
            writeln!(stream, "NOT-A-RESERVATION").expect("write malformed response");
            stream.flush().expect("flush malformed response");
            let _ = stop_rx.recv();
        });

        // The malformed REPLY is the refusal under test, so the client runs on
        // the test's own deadline: with the production one, a loaded host can
        // expire it first and pass this test for the wrong reason. The 500 ms
        // bound keeps its dedicated coverage in
        // `configured_hung_daemon_fails_without_minting_file_capacity`.
        let error =
            reserve_labeled_with(4096, "malformed", TEST_OBSERVER_TIMEOUT, machine_budget_bytes)
                .expect_err("a malformed selected daemon must block solver launch");
        stop_tx.send(()).expect("release malformed responder");
        server.join().expect("malformed responder joined");
        assert!(
            error.to_string().contains("invalid STATUS reply"),
            "unexpected configured-daemon failure: {error}"
        );
        file_lane.assert_no_token_minted();
    }

    #[test]
    fn configured_daemon_decline_fails_without_minting_file_capacity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Supply the machine total, as this test already supplies a socket and a
        // token path. Without it `machine_budget_bytes()` is 0 wherever the visible
        // cgroup root has no `memory.max` (every bare-metal cgroup-v2 Linux box), and
        // the admission this test exists to exercise is refused before it begins.
        // NOT the fail-closed cgroup exemption — that rule governs production.
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("declined-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind declining responder");
        make_socket_private(&fixture.path);
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let file_lane = TestFileLane::new("declined");
        file_lane.prove_lane_would_grant_then_reset(4096);

        let daemon = test_daemon(1024);
        let server = spawn_ready_responder(move || {
            let (stream, _) = listener.accept().expect("accept declined reserve client");
            daemon.serve_conn(stream);
        });

        // DEGRADED is the refusal under test; measured failing under load with
        // the production deadline instead ("did not return one complete STATUS
        // reply before the deadline"), which passed `expect_err` and then broke
        // on this assertion. The client therefore runs on the test's deadline.
        let error =
            reserve_labeled_with(4096, "too-large", TEST_OBSERVER_TIMEOUT, machine_budget_bytes)
                .expect_err("DEGRADED from a selected daemon must block solver launch");
        assert!(
            error.to_string().contains("declined the reservation"),
            "the daemon's DEGRADED answer is what refuses this: {error}"
        );
        file_lane.assert_no_token_minted();
        server.join().expect("declining responder joined");
    }

    #[test]
    fn configured_over_connection_limit_fails_without_minting_file_capacity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Supply the machine total, as this test already supplies a socket and a
        // token path. Without it `machine_budget_bytes()` is 0 wherever the visible
        // cgroup root has no `memory.max` (every bare-metal cgroup-v2 Linux box), and
        // the admission this test exists to exercise is refused before it begins.
        // NOT the fail-closed cgroup exemption — that rule governs production.
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let fixture = TestSocket::new("busy-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind busy responder");
        make_socket_private(&fixture.path);
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let file_lane = TestFileLane::new("busy");
        file_lane.prove_lane_would_grant_then_reset(4096);

        let daemon = test_daemon(64 << 10);
        let permits: Vec<_> = (0..MAX_SERVER_CONNECTIONS)
            .map(|_| daemon.try_acquire_connection().expect("fill connection slot"))
            .collect();
        let server = spawn_ready_responder(move || {
            let (stream, _) = listener.accept().expect("accept over-limit client");
            let error = daemon
                .admit_connection(stream)
                .err()
                .expect("the sixty-fifth connection is rejected");
            assert_eq!(
                error.kind(),
                std::io::ErrorKind::WouldBlock,
                "a connection-limit rejection is WouldBlock, not {error}"
            );
            drop(permits);
        });

        // `ERR busy` is the refusal under test, so the client runs on the
        // test's deadline rather than the production 500 ms one.
        let error =
            reserve_labeled_with(4096, "sixty-fifth", TEST_OBSERVER_TIMEOUT, machine_budget_bytes)
                .expect_err("ERR busy from a selected daemon must block solver launch");
        assert!(
            error.to_string().contains("ERR busy"),
            "the saturated daemon's framed rejection is what refuses this: {error}"
        );
        file_lane.assert_no_token_minted();
        server.join().expect("busy responder joined");
    }

    #[test]
    fn status_is_a_pure_snapshot() {
        let d = test_daemon(1 << 30);
        // STATUS reports state without interpreting the diagnostic PID or
        // otherwise changing admission.
        let reply = d.handle_line(&format!("RESERVE 4096 {} worker", synthetic_protocol_pid()));
        assert!(reply.starts_with("GRANTED "));

        let before = {
            let st = d.lock();
            (st.reserved_bytes, st.released_total, st.active.len())
        };
        let line = d.handle_line("STATUS");
        let parsed: DaemonStatus = serde_json::from_str(&line).expect("valid status json");
        let after = {
            let st = d.lock();
            (st.reserved_bytes, st.released_total, st.active.len())
        };

        assert_eq!(before, (4096, 0, 1));
        assert_eq!(after, before, "STATUS must not mutate budget state");
        assert_eq!(parsed.reserved_bytes, 4096);
        assert_eq!(parsed.active.len(), 1);
    }

    #[test]
    fn status_and_ping_do_not_extend_idle_lifetime() {
        let d = test_daemon(1 << 30);
        {
            let mut activity = d.last_activity.lock().unwrap_or_else(|e| e.into_inner());
            *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
        }
        assert!(d.idle_expired(), "fixture starts beyond the idle bound");

        let _ = d.handle_line("STATUS");
        assert!(d.idle_expired(), "STATUS must not refresh daemon activity");
        assert_eq!(d.handle_line("PING"), "PONG");
        assert!(d.idle_expired(), "PING must not refresh daemon activity");

        // A worker operation, including an inert zero-byte reservation, is
        // intentionally different: it proves the daemon is still in use.
        assert_eq!(d.handle_line("RESERVE 0 1 worker"), "GRANTED 0");
        assert!(!d.idle_expired(), "worker traffic refreshes daemon activity");
    }

    #[test]
    fn queued_reservation_prevents_idle_shutdown() {
        let d = test_daemon(1 << 30);
        {
            let mut activity = d.last_activity.lock().unwrap_or_else(|e| e.into_inner());
            *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
        }
        {
            let mut st = d.lock();
            st.queue_depth = 1;
        }
        assert!(
            !d.idle_expired(),
            "a parked RESERVE is live admission work even when active is empty"
        );

        d.lock().queue_depth = 0;
        assert!(d.idle_expired(), "the old idle deadline applies once the queue drains");
    }

    #[test]
    fn quiescent_shutdown_closes_admission_before_clean_epoch_is_possible() {
        let d = test_daemon(1 << 30);
        {
            let mut activity = d.last_activity.lock().unwrap_or_else(|e| e.into_inner());
            *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
        }
        assert!(d.try_begin_idle_shutdown(), "empty expired ledger may close admission");
        assert_eq!(
            d.handle_line("RESERVE 4096 1 too-late"),
            "DEGRADED",
            "no grant may race after the quiescent shutdown proof"
        );
        assert_eq!(d.lock().reserved_bytes, 0);
    }

    /// Age the daemon's activity clock past [`IDLE_TIMEOUT`]: what a compile
    /// that sends no admission traffic for that long leaves behind.
    fn outlast_the_idle_bound(d: &Daemon) {
        let mut activity = d.last_activity.lock().unwrap_or_else(|e| e.into_inner());
        *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
    }

    /// One reply line under the protocol tests' own deadline, not the
    /// production observer bound (see [`TEST_OBSERVER_TIMEOUT`]).
    fn read_reply(stream: &UnixStream) -> Option<String> {
        let deadline =
            Instant::now().checked_add(TEST_OBSERVER_TIMEOUT).unwrap_or_else(Instant::now);
        read_one_line_until(stream, deadline)
    }

    /// The 0.11.0 consumer check (2026-10-19). targo selected this daemon and
    /// exported its socket; aterm's binary then compiled past the idle bound
    /// with no admission traffic; the daemon took its idle shutdown and
    /// recorded CLEAN; and the unit's first admission met ECONNREFUSED on the
    /// selected endpoint, so all 129 of its obligations were refused. The
    /// session's lease must hold the daemon through that window, past the
    /// initial-client read timeout too, and its end must leave the daemon free
    /// to idle out as before.
    #[test]
    fn a_session_lease_holds_the_daemon_through_a_compile_longer_than_the_idle_bound() {
        let d = test_daemon(1 << 30);
        let (mut session, server) = UnixStream::pair().expect("UnixStream pair");
        // Queue the frame before the handler starts, so its tiny initial read
        // timeout cannot race this thread.
        writeln!(session, "LEASE").expect("send LEASE");
        session.flush().expect("flush LEASE");
        let handler = {
            let d = Arc::clone(&d);
            thread::spawn(move || {
                d.serve_conn_with_read_timeouts(server, Duration::from_millis(25), None)
            })
        };
        let leased = read_reply(&session);

        // The unit compiles: no frame on any connection for longer than both
        // the initial read timeout and the idle bound.
        thread::sleep(Duration::from_millis(100));
        outlast_the_idle_bound(&d);
        assert!(
            !d.try_begin_idle_shutdown(),
            "a live session's daemon must not idle out under it (LEASE answered {leased:?})"
        );
        assert_eq!(leased.as_deref(), Some("LEASED"));
        let late = d.handle_line(&format!("RESERVE 4096 {} late-unit", synthetic_protocol_pid()));
        let token = late
            .strip_prefix("GRANTED ")
            .and_then(|token| token.parse::<u64>().ok())
            .expect("the unit that compiled past the idle bound is admitted");
        assert_eq!(d.handle_line(&format!("RELEASE {token}")), "OK");

        // The session ends, by whatever path: EOF ends its lease, and the idle
        // interval counts from then, not from the last admission.
        outlast_the_idle_bound(&d);
        drop(session);
        handler.join().expect("lease handler joined at EOF");
        assert!(!d.idle_expired(), "the idle interval restarts when the last session ends");
        outlast_the_idle_bound(&d);
        assert!(d.try_begin_idle_shutdown(), "an ended session holds nothing");
    }

    /// Once the idle proof has closed admission the daemon is about to record
    /// CLEAN and exit, so it refuses a lease: the launcher establishes a
    /// successor instead of exporting an endpoint that is about to die.
    #[test]
    fn a_lease_never_follows_the_clean_shutdown_proof() {
        let d = test_daemon(1 << 30);
        outlast_the_idle_bound(&d);
        assert!(d.try_begin_idle_shutdown(), "an unleased, expired daemon closes admission");
        let (mut launcher, server) = UnixStream::pair().expect("UnixStream pair");
        let handler = {
            let d = Arc::clone(&d);
            thread::spawn(move || d.serve_conn(server))
        };
        writeln!(launcher, "LEASE").expect("send LEASE");
        launcher.flush().expect("flush LEASE");
        assert_eq!(read_reply(&launcher).as_deref(), Some("DEGRADED"));
        drop(launcher);
        handler.join().expect("refused lease handler joined");
    }

    /// One lease per connection, minted only by the connection layer: a bare
    /// frame has no EOF to end it, and a second LEASE on one connection must
    /// not count twice, or the daemon would stay held after its session ended.
    #[test]
    fn a_lease_is_owned_by_exactly_one_connection() {
        let d = test_daemon(1 << 30);
        assert_eq!(d.handle_line("LEASE"), "ERR connection-owned");
        assert_eq!(d.handle_line("LEASE forever"), "ERR bad-args");

        let (mut session, server) = UnixStream::pair().expect("UnixStream pair");
        let handler = {
            let d = Arc::clone(&d);
            thread::spawn(move || d.serve_conn(server))
        };
        for expected in ["LEASED", "ERR outstanding-lease"] {
            writeln!(session, "LEASE").expect("send LEASE");
            session.flush().expect("flush LEASE");
            assert_eq!(read_reply(&session).as_deref(), Some(expected));
        }
        drop(session);
        handler.join().expect("lease handler joined at EOF");
        outlast_the_idle_bound(&d);
        assert!(d.try_begin_idle_shutdown(), "the ended session's one lease was its only one");
    }

    /// Readiness is the lease, taken on the connection that authenticated the
    /// daemon, so `ensure_daemon` hands its caller a hold on exactly that
    /// daemon, and the hold is the connection.
    #[test]
    fn adopting_a_compatible_daemon_holds_it_until_the_lease_drops() {
        let fixture = TestSocket::new("lease-adopt");
        let listener = UnixListener::bind(&fixture.path).expect("bind lease server");
        make_socket_private(&fixture.path);
        let identity = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: compiled_release().to_string(),
            commit: compiled_commit().to_string(),
            executable_sha256: "d".repeat(64),
        };
        let daemon = Daemon::with_budget_and_identity(4096, identity.clone());
        let served = Arc::clone(&daemon);
        let server = spawn_ready_responder(move || {
            let (stream, _) = listener.accept().expect("accept adopting launcher");
            served.serve_conn(stream);
        });

        let deadline =
            Instant::now().checked_add(TEST_OBSERVER_TIMEOUT).unwrap_or_else(Instant::now);
        let lease = lease_compatible_daemon_until_with_budget_source(
            &fixture.path,
            &identity,
            deadline,
            || 4096,
        )
        .expect("an exact daemon within the client budget is adopted and leased");
        outlast_the_idle_bound(&daemon);
        assert!(!daemon.try_begin_idle_shutdown(), "the adopted daemon is held");
        drop(lease);
        server.join().expect("lease server joined at EOF");
        outlast_the_idle_bound(&daemon);
        assert!(daemon.try_begin_idle_shutdown(), "a dropped lease holds nothing");
    }

    /// `serve` drains on endpoint loss whatever is leased, so only a definite
    /// answer that the path no longer reaches its listener may read as loss.
    /// A stat that failed is no such answer: read as loss, one EIO would end
    /// a leased daemon between two admissions, and every later unit of the
    /// session would meet ECONNREFUSED.
    #[test]
    fn only_a_definite_answer_reads_as_endpoint_loss() {
        let fixture = TestSocket::new("endpoint-check");
        let _listener = UnixListener::bind(&fixture.path).expect("bind endpoint");
        make_socket_private(&fixture.path);
        let published = socket_identity_at(&fixture.path)
            .expect("stat endpoint")
            .expect("the endpoint is a private socket");
        let check = |path: &Path| endpoint_check(std::fs::symlink_metadata(path), published);
        assert_eq!(check(&fixture.path), EndpointCheck::Intact);
        for errno in [libc::EIO, libc::ENOMEM] {
            let failed = Err(std::io::Error::from_raw_os_error(errno));
            assert_eq!(endpoint_check(failed, published), EndpointCheck::Unobserved, "{errno}");
        }

        std::fs::set_permissions(&fixture.path, std::fs::Permissions::from_mode(0o666))
            .expect("open the endpoint to others");
        assert_eq!(check(&fixture.path), EndpointCheck::Lost, "a non-private endpoint");
        // The listener stays bound, so its inode cannot be reused below.
        std::fs::remove_file(&fixture.path).expect("unlink endpoint");
        assert_eq!(check(&fixture.path), EndpointCheck::Lost, "a missing endpoint");
        let successor = UnixListener::bind(&fixture.path).expect("bind successor");
        make_socket_private(&fixture.path);
        assert_eq!(check(&fixture.path), EndpointCheck::Lost, "another listener's socket");
        drop(successor);
        std::fs::remove_file(&fixture.path).expect("unlink successor");
        File::create(&fixture.path).expect("replace the endpoint with a file");
        assert_eq!(check(&fixture.path), EndpointCheck::Lost, "a non-socket");
        assert_eq!(check(&fixture.path.join("below")), EndpointCheck::Lost, "ENOTDIR");
    }

    #[test]
    fn dynamic_refresh_cannot_grant_after_concurrent_clean_shutdown_proof() {
        let identity = DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: compiled_release().to_string(),
            commit: compiled_commit().to_string(),
            executable_sha256: "0".repeat(64),
        };
        let d = Daemon::with_budget_policy(1 << 30, identity, BudgetPolicy::DynamicMachine);
        {
            let mut activity = d.last_activity.lock().unwrap_or_else(|e| e.into_inner());
            *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
        }
        let gate = Arc::new(RefreshTestGate {
            observed: std::sync::Barrier::new(2),
            resume: std::sync::Barrier::new(2),
        });
        *d.refresh_test_gate.lock().unwrap_or_else(|e| e.into_inner()) = Some(Arc::clone(&gate));

        let worker = {
            let d = Arc::clone(&d);
            thread::spawn(move || d.reserve(1, 1, "refresh-race".to_string()))
        };
        gate.observed.wait();
        assert!(
            d.try_begin_idle_shutdown(),
            "refresh dropped the empty ledger so shutdown can close admission"
        );
        gate.resume.wait();
        assert_eq!(worker.join().expect("refreshing reserve joined"), "DEGRADED");
        assert_eq!(d.lock().reserved_bytes, 0, "CLEAN proof cannot be followed by a grant");
    }

    #[test]
    fn connection_limit_is_exact_and_overflow_gets_busy() {
        let d = test_daemon(1 << 30);
        let permits: Vec<_> = (0..MAX_SERVER_CONNECTIONS)
            .map(|_| d.try_acquire_connection().expect("slot below the hard limit"))
            .collect();
        assert_eq!(d.active_connections.load(AtomicOrdering::Acquire), MAX_SERVER_CONNECTIONS);
        assert!(d.try_acquire_connection().is_none(), "the next connection is refused");

        let (client, server) = UnixStream::pair().expect("UnixStream pair");
        let saturated = Arc::clone(&d);
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        let rejector = thread::spawn(move || {
            let result = match saturated.admit_connection(server) {
                Ok(_) => Err("an over-limit stream was assigned a handler".to_string()),
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => Ok(()),
                Err(error) => Err(format!("busy-frame transport failed: {error}")),
            };
            result_tx.send(result).expect("report busy admission result");
        });
        assert_eq!(read_one_line(&client).as_deref(), Some("ERR busy"));
        drop(client);
        result_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("bounded busy handshake completed")
            .expect("busy admission wrote its complete response");
        rejector.join().expect("busy rejector joined");

        drop(permits);
        assert_eq!(d.active_connections.load(AtomicOrdering::Acquire), 0);
        let recycled = d.try_acquire_connection().expect("dropping a permit returns its slot");
        drop(recycled);
        assert_eq!(d.active_connections.load(AtomicOrdering::Acquire), 0);
    }

    /// The platform fact `reject_busy_connection` has to classify: once the
    /// peer closes, a Unix socket reports the disconnect from `setsockopt`
    /// itself, before any read is attempted. macOS answers `EINVAL`, which Rust
    /// surfaces as `InvalidInput` — indistinguishable by kind from "you passed
    /// a zero timeout", which is why that call site must pass a provably
    /// nonzero one. A platform that accepts the call has nothing to classify.
    #[test]
    fn a_closed_peer_can_be_reported_by_setsockopt_before_any_read() {
        let (client, server) = UnixStream::pair().expect("UnixStream pair");
        drop(client);
        if let Err(error) = server.set_read_timeout(Some(OBSERVER_IO_TIMEOUT)) {
            assert!(
                busy_peer_has_left(&error),
                "a closed peer is not a transport failure: {error} ({:?})",
                error.kind()
            );
        }
    }

    /// A client that consumes `ERR busy` and closes *promptly* is the
    /// well-behaved one, and it must not turn the rejection into a transport
    /// error: the connection-limit answer is `WouldBlock` on every round, never
    /// a kind that depends on which side the scheduler ran first.
    #[test]
    fn a_prompt_client_close_still_reports_the_connection_limit_as_would_block() {
        const ROUNDS: usize = 64;
        let d = test_daemon(1 << 30);
        let permits: Vec<_> = (0..MAX_SERVER_CONNECTIONS)
            .map(|_| d.try_acquire_connection().expect("fill connection slot"))
            .collect();

        for round in 0..ROUNDS {
            let (client, server) = UnixStream::pair().expect("UnixStream pair");
            let saturated = Arc::clone(&d);
            let rejector = thread::spawn(move || saturated.admit_connection(server).err());

            let mut frame = String::new();
            BufReader::new(client.try_clone().expect("clone busy client"))
                .read_line(&mut frame)
                .expect("read the busy frame");
            assert_eq!(frame, "ERR busy\n", "round {round}: the rejection is framed");
            // One byte forces the accept thread round its drain loop again, so
            // the close below lands BEFORE the next `set_read_timeout` — the
            // order that used to be misreported as an I/O failure.
            let mut writer = client;
            let _ = writer.write_all(b"x");
            drop(writer);

            let error = rejector
                .join()
                .expect("busy rejector joined")
                .expect("an over-limit stream is never assigned a handler");
            assert_eq!(
                error.kind(),
                std::io::ErrorKind::WouldBlock,
                "round {round}: a connection-limit rejection is WouldBlock, not {error}"
            );
        }

        drop(permits);
        assert_eq!(d.active_connections.load(AtomicOrdering::Acquire), 0);
    }

    #[test]
    fn idle_connection_read_timeout_releases_handler() {
        let d = test_daemon(1 << 30);
        let (_idle_client, server) = UnixStream::pair().expect("UnixStream pair");
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let handler = thread::spawn(move || {
            d.serve_conn_with_read_timeout(server, Duration::from_millis(50));
            done_tx.send(()).expect("report handler exit");
        });

        done_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("an idle peer cannot retain its handler past the read timeout");
        handler.join().expect("timed-out handler joined");
    }

    #[test]
    fn granted_connection_clears_initial_idle_timeout() {
        let d = test_daemon(1 << 30);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        // Queue the first frame before starting the handler so this test has no
        // scheduler race against its intentionally tiny initial timeout.
        writeln!(client, "RESERVE 4096 {} timeout-promotion", std::process::id())
            .expect("send RESERVE");
        client.flush().expect("flush RESERVE");
        let handler = thread::spawn(move || {
            d.serve_conn_with_read_timeouts(server, Duration::from_millis(25), None);
            done_tx.send(()).expect("report handler exit");
        });

        let granted = read_one_line(&client).expect("read GRANTED");
        let token = granted
            .strip_prefix("GRANTED ")
            .expect("reservation granted")
            .parse::<u64>()
            .expect("numeric token");

        // Wait well past the initial-client timeout. A legitimate granted
        // reservation must clear that timeout entirely: proof duration is not a
        // lease, and its matching RELEASE uses this connection as ownership.
        thread::sleep(Duration::from_millis(100));
        writeln!(client, "RELEASE {token}").expect("send RELEASE after initial timeout");
        client.flush().expect("flush RELEASE");
        assert_eq!(read_one_line(&client).as_deref(), Some("OK"));

        // Once no grant is live, this peer is an ordinary idle client again.
        // It must lose the handler slot even if it keeps its socket open.
        done_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("a post-release idle peer cannot retain its handler indefinitely");
        drop(client);
        handler.join().expect("post-release timeout handler joined");
    }

    #[test]
    fn connection_close_releases_owned_grants() {
        let d = test_daemon(1 << 30);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let d2 = Arc::clone(&d);
        let handler = thread::spawn(move || d2.serve_conn(server));

        writeln!(client, "RESERVE 4096 {} disconnect", std::process::id()).expect("send RESERVE");
        client.flush().expect("flush RESERVE");
        assert!(
            read_one_line(&client).is_some_and(|reply| reply.starts_with("GRANTED ")),
            "reservation granted before disconnect"
        );
        {
            let state = d.lock();
            assert_eq!(state.reserved_bytes, 4096);
            assert_eq!(state.active.len(), 1);
        }

        // No RELEASE frame: EOF itself ends this connection-owned lease.
        drop(client);
        handler.join().expect("disconnected reservation handler joined");
        let state = d.lock();
        assert_eq!(state.reserved_bytes, 0);
        assert!(state.active.is_empty());
        assert_eq!(state.granted_total, 1);
        assert_eq!(state.released_total, 1);
        assert!(state.snapshot().has_valid_invariants());
    }

    #[test]
    fn one_connection_cannot_accumulate_unbounded_live_grants() {
        let d = test_daemon(1 << 30);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let server_daemon = Arc::clone(&d);
        let handler = thread::spawn(move || server_daemon.serve_conn(server));

        writeln!(client, "RESERVE 1 {} first", std::process::id()).expect("send first RESERVE");
        client.flush().expect("flush first RESERVE");
        let first_token = read_one_line(&client)
            .and_then(|reply| reply.strip_prefix("GRANTED ").map(str::to_string))
            .and_then(|token| token.parse::<u64>().ok())
            .expect("first reservation granted");

        writeln!(client, "RESERVE 1 {} duplicate", std::process::id())
            .expect("send duplicate RESERVE");
        client.flush().expect("flush duplicate RESERVE");
        assert_eq!(read_one_line(&client).as_deref(), Some("ERR outstanding-grant"));
        {
            let state = d.lock();
            assert_eq!(state.active.len(), 1, "connection ownership is structurally bounded");
            assert_eq!(state.reserved_bytes, 1);
            assert_eq!(state.granted_total, 1);
        }

        writeln!(client, "RELEASE {first_token}").expect("release first grant");
        client.flush().expect("flush first RELEASE");
        assert_eq!(read_one_line(&client).as_deref(), Some("OK"));

        writeln!(client, "RESERVE 2 {} after-release", std::process::id())
            .expect("send post-release RESERVE");
        client.flush().expect("flush post-release RESERVE");
        let second_token = read_one_line(&client)
            .and_then(|reply| reply.strip_prefix("GRANTED ").map(str::to_string))
            .and_then(|token| token.parse::<u64>().ok())
            .expect("a released connection may reserve again");
        {
            let state = d.lock();
            assert_eq!(state.active.len(), 1);
            assert_eq!(state.reserved_bytes, 2);
            assert_eq!(state.granted_total, 2);
            assert_eq!(state.released_total, 1);
        }

        writeln!(client, "RELEASE {second_token}").expect("release second grant");
        client.flush().expect("flush second RELEASE");
        assert_eq!(read_one_line(&client).as_deref(), Some("OK"));
        drop(client);
        handler.join().expect("bounded-grant handler joined");
        let state = d.lock();
        assert!(state.active.is_empty());
        assert_eq!(state.reserved_bytes, 0);
        assert_eq!(state.released_total, 2);
        assert!(state.snapshot().has_valid_invariants());
    }

    #[test]
    fn inherited_socket_fd_keeps_grant_until_solver_child_exits() {
        let d = test_daemon(1 << 20);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let server_daemon = Arc::clone(&d);
        let handler = thread::spawn(move || server_daemon.serve_conn(server));
        writeln!(client, "RESERVE 4096 {} child-guard", std::process::id()).expect("send RESERVE");
        client.flush().expect("flush RESERVE");
        assert!(
            read_one_line(&client).is_some_and(|reply| reply.starts_with("GRANTED ")),
            "reservation granted before simulated parent death"
        );

        // A held stdin keeps the child alive across test-thread scheduling
        // stalls. No timed fuse can expire before the mid-flight assertions.
        let mut command = std::process::Command::new("/bin/cat");
        command.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::null());
        inherit_fd_across_exec(&mut command, client.as_raw_fd())
            .expect("retain child guard descriptor");
        let mut child = TestChild(command.spawn().expect("spawn child with inherited guard fd"));
        drop(command);
        // Simulate an abrupt parent exit: close without a RELEASE frame. The
        // child duplicate must prevent server EOF and premature readmission.
        drop(client);
        thread::sleep(Duration::from_millis(50));
        {
            let state = d.lock();
            assert_eq!(state.reserved_bytes, 4096);
            assert_eq!(state.active.len(), 1);
            assert_eq!(state.released_total, 0);
        }

        // Already-exited is fine: the EOF assertions below are the verdict,
        // and a kill failure here must not become a new fuse.
        let _ = child.0.kill();
        child.0.wait().expect("wait guarded child");
        handler.join().expect("handler observes final inherited-fd close");
        let state = d.lock();
        assert_eq!(state.reserved_bytes, 0);
        assert!(state.active.is_empty());
        assert_eq!(state.released_total, 1);
    }

    #[test]
    fn command_owns_stable_guard_fd_if_reservation_drops_before_spawn() {
        let d = test_daemon(1 << 20);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let server_daemon = Arc::clone(&d);
        let handler = thread::spawn(move || server_daemon.serve_conn(server));
        writeln!(client, "RESERVE 4096 {} command-guard", std::process::id())
            .expect("send RESERVE");
        client.flush().expect("flush RESERVE");
        let reply = read_one_line(&client).expect("read grant");
        let token = reply
            .strip_prefix("GRANTED ")
            .and_then(|value| value.parse::<u64>().ok())
            .expect("nonzero grant token");
        let mut reservation = Reservation {
            inner: ReservationKind::Daemon {
                stream: client,
                token,
                bytes: 4096,
                owner_pid: std::process::id(),
                explicit_release_on_drop: true,
            },
        };
        // Hold the child on stdin until its explicit cleanup, without a
        // scheduling-dependent natural exit that could look like early EOF.
        let mut command = std::process::Command::new("/bin/cat");
        command.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::null());
        reservation
            .configure_child_lifetime_guard(&mut command)
            .expect("Command takes structural ownership of a stable descriptor");

        drop(reservation);
        assert_eq!(
            d.lock().reserved_bytes,
            4096,
            "dropping Reservation cannot close the Command-owned connection"
        );
        let mut child = TestChild(command.spawn().expect("spawn after Reservation drop"));
        drop(command);
        thread::sleep(Duration::from_millis(50));
        assert_eq!(d.lock().reserved_bytes, 4096, "child inherited the stable descriptor");

        let _ = child.0.kill();
        child.0.wait().expect("wait guarded child");
        handler.join().expect("handler observes final guarded EOF");
        assert_eq!(d.lock().reserved_bytes, 0);
    }

    #[test]
    fn child_bound_reservation_waits_for_descendant_eof_instead_of_releasing_on_drop() {
        let d = test_daemon(1 << 20);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let server_daemon = Arc::clone(&d);
        let handler = thread::spawn(move || server_daemon.serve_conn(server));
        writeln!(client, "RESERVE 4096 {} descendant-guard", std::process::id())
            .expect("send RESERVE");
        client.flush().expect("flush RESERVE");
        let reply = read_one_line(&client).expect("read grant");
        let token = reply
            .strip_prefix("GRANTED ")
            .and_then(|value| value.parse::<u64>().ok())
            .expect("nonzero grant token");

        let mut reservation = Reservation {
            inner: ReservationKind::Daemon {
                stream: client,
                token,
                bytes: 4096,
                owner_pid: std::process::id(),
                explicit_release_on_drop: true,
            },
        };
        // The descendant waits for EOF on a separate control socket. Its
        // lifetime has no timer, PID file, or signal to a possibly reused PID.
        let (control, reader) = UnixStream::pair().expect("descendant control pair");
        let mut command = std::process::Command::new("/bin/sh");
        command
            .args(["-c", "cat <&2 >/dev/null 2>/dev/null & exit 0"])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::from(std::os::fd::OwnedFd::from(reader)));
        // Stdio carries the control reader in descriptor 2, which the child
        // duplicates to stdin before discarding stderr. This also works in
        // shells that replace background stdin before interpreting `<&0`.
        reservation.configure_child_lifetime_guard(&mut command).expect("install child EOF guard");
        let mut leader = TestChild(command.spawn().expect("spawn solver leader and descendant"));
        drop(command);
        leader.0.wait().expect("reap exited leader");

        // The leader has exited, but its background descendant still owns the
        // inherited descriptor. Drop must close the parent copy without sending
        // RELEASE; the daemon retains capacity until that final kernel EOF.
        drop(reservation);
        thread::sleep(Duration::from_millis(75));
        {
            let state = d.lock();
            assert_eq!(state.reserved_bytes, 4096);
            assert_eq!(state.active.len(), 1);
            assert_eq!(state.released_total, 0);
        }

        drop(control); // EOF releases only this test's descendant.
        handler.join().expect("handler observes descendant's final EOF");
        let state = d.lock();
        assert_eq!(state.reserved_bytes, 0);
        assert!(state.active.is_empty());
        assert_eq!(state.released_total, 1);
    }

    #[test]
    fn active_file_reservation_refuses_external_child_spawn() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Supply the machine total, as this test already supplies a socket and a
        // token path. Without it `machine_budget_bytes()` is 0 wherever the visible
        // cgroup root has no `memory.max` (every bare-metal cgroup-v2 Linux box), and
        // the admission this test exists to exercise is refused before it begins.
        // NOT the fail-closed cgroup exemption — that rule governs production.
        let _budget = memory_jobserver::TestTotalMemory::set(1 << 30);
        let _socket = ScopedEnvOverride::remove(SOCK_ENV);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let _file_lane = TestFileLane::new("child-lifetime");
        let mut reservation = reserve(4096).expect("file authority admits test reservation");
        assert!(reservation.is_active());
        let mut command = std::process::Command::new("/usr/bin/true");
        let error = reservation
            .configure_child_lifetime_guard(&mut command)
            .expect_err("parent-PID file row cannot authorize an external child");
        assert!(error.contains("cannot atomically bind"));
    }

    #[test]
    fn live_connection_cannot_release_another_connections_grant() {
        let d = test_daemon(1 << 30);
        let (mut owner_client, owner_server) = UnixStream::pair().expect("owner stream pair");
        let (mut foreign_client, foreign_server) = UnixStream::pair().expect("foreign stream pair");
        let owner_daemon = Arc::clone(&d);
        let owner_handler = thread::spawn(move || owner_daemon.serve_conn(owner_server));
        let foreign_daemon = Arc::clone(&d);
        let foreign_handler = thread::spawn(move || foreign_daemon.serve_conn(foreign_server));

        writeln!(owner_client, "RESERVE 4096 {} owner", std::process::id())
            .expect("send owner RESERVE");
        owner_client.flush().expect("flush owner RESERVE");
        let token = read_one_line(&owner_client)
            .and_then(|reply| reply.strip_prefix("GRANTED ").map(str::to_string))
            .and_then(|token| token.parse::<u64>().ok())
            .expect("owner receives a numeric grant token");

        // STATUS intentionally exposes tokens for diagnostics; possession of
        // that number on another connection must not authorize a release.
        writeln!(foreign_client, "RELEASE {token}").expect("send foreign RELEASE");
        foreign_client.flush().expect("flush foreign RELEASE");
        assert_eq!(read_one_line(&foreign_client).as_deref(), Some("ERR unowned-token"));
        {
            let state = d.lock();
            assert_eq!(state.reserved_bytes, 4096);
            assert_eq!(state.active.len(), 1);
            assert_eq!(state.active[0].token, token);
            assert_eq!(state.released_total, 0);
        }

        writeln!(owner_client, "RELEASE {token}").expect("send owning RELEASE");
        owner_client.flush().expect("flush owning RELEASE");
        assert_eq!(read_one_line(&owner_client).as_deref(), Some("OK"));
        drop(foreign_client);
        drop(owner_client);
        foreign_handler.join().expect("foreign handler joined");
        owner_handler.join().expect("owner handler joined");
        let state = d.lock();
        assert_eq!(state.reserved_bytes, 0);
        assert!(state.active.is_empty());
        assert_eq!(state.granted_total, 1);
        assert_eq!(state.released_total, 1);
        assert!(state.snapshot().has_valid_invariants());
    }

    #[test]
    fn observational_socket_connection_does_not_extend_idle_lifetime() {
        let d = test_daemon(1 << 30);
        {
            let mut activity = d.last_activity.lock().unwrap_or_else(|e| e.into_inner());
            *activity = unix_now().saturating_sub(IDLE_TIMEOUT.as_secs());
        }

        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let d2 = Arc::clone(&d);
        let server_thread = thread::spawn(move || d2.serve_conn(server));
        writeln!(client, "STATUS").expect("write STATUS");
        client.flush().expect("flush STATUS");
        let line = read_one_line(&client).expect("read STATUS");
        let _: DaemonStatus = serde_json::from_str(&line).expect("valid status json");
        drop(client);
        server_thread.join().expect("server thread joined");

        assert!(d.idle_expired(), "opening and closing an observer connection is inert");
    }

    #[test]
    fn client_reported_pid_and_age_never_control_grant_lifetime() {
        let d = test_daemon(1 << 30);
        let (mut client, server) = UnixStream::pair().expect("UnixStream pair");
        let server_daemon = Arc::clone(&d);
        let handler = thread::spawn(move || server_daemon.serve_conn(server));
        writeln!(client, "RESERVE 4096 {} foreign-namespace-number", synthetic_protocol_pid())
            .expect("send RESERVE with synthetic PID");
        client.flush().expect("flush RESERVE");
        let token = read_one_line(&client)
            .and_then(|reply| reply.strip_prefix("GRANTED ").map(str::to_string))
            .and_then(|token| token.parse::<u64>().ok())
            .expect("synthetic PID still receives a connection-owned grant");
        {
            let mut st = d.lock();
            st.active[0].granted_at = Instant::now()
                .checked_sub(Duration::from_secs(31 * 60))
                .expect("monotonic clock has 31 minutes of range");
        }

        d.refresh_budget_ceiling();

        {
            let st = d.lock();
            assert_eq!(st.active.len(), 1, "PID and age cannot reclaim a live connection");
            assert_eq!(st.reserved_bytes, 4096);
            assert_eq!(st.released_total, 0);
        }
        writeln!(client, "RELEASE {token}").expect("release owning grant");
        client.flush().expect("flush RELEASE");
        assert_eq!(read_one_line(&client).as_deref(), Some("OK"));
        drop(client);
        handler.join().expect("handler joined");
    }

    #[test]
    fn connection_grant_guard_releases_during_unwind() {
        let d = test_daemon(1 << 30);
        let reply = d.handle_line(&format!("RESERVE 4096 {} unwind", std::process::id()));
        let token = reply
            .strip_prefix("GRANTED ")
            .and_then(|token| token.parse::<u64>().ok())
            .expect("direct grant token");
        let guarded_daemon = Arc::clone(&d);
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let mut grants = ConnectionGrants::new(guarded_daemon);
            grants.insert(token);
            panic!("exercise connection cleanup unwind");
        }));
        assert!(unwind.is_err());
        let st = d.lock();
        assert_eq!(st.reserved_bytes, 0);
        assert!(st.active.is_empty());
        assert_eq!(st.released_total, 1);
    }

    #[test]
    fn unknown_verb_and_bad_args_err() {
        let d = test_daemon(1 << 30);
        assert_eq!(d.handle_line("FOOBAR"), "ERR unknown-verb");
        assert_eq!(d.handle_line("RESERVE notanumber 1 x"), "ERR bad-bytes");
        assert_eq!(d.handle_line("RESERVE 1024 notapid x"), "ERR bad-pid");
        assert_eq!(d.handle_line("RESERVE 1024 0 x"), "ERR bad-pid");
        assert_eq!(
            d.handle_line(&format!("RESERVE 1024 {} x", i32::MAX as u32 + 1)),
            "ERR bad-pid"
        );
        assert_eq!(d.handle_line("RELEASE notatoken"), "ERR bad-token");
        assert_eq!(d.handle_line("RELEASE 1 trailing"), "ERR bad-token");
        assert_eq!(d.handle_line("STATUS trailing"), "ERR bad-args");
        assert_eq!(d.handle_line("PING trailing"), "ERR bad-args");
    }

    #[test]
    fn long_line_rejected() {
        let d = test_daemon(1 << 30);
        let long = format!("RESERVE 1 1 {}", "a".repeat(MAX_REQUEST_BYTES + 10));
        assert_eq!(d.handle_line(&long), "ERR line-too-long");
    }

    #[test]
    fn label_truncated_to_cap() {
        let d = test_daemon(1 << 30);
        let label = "b".repeat(MAX_LABEL_BYTES + 50);
        let reply = d.handle_line(&format!("RESERVE 4096 1234 {label}"));
        assert!(reply.starts_with("GRANTED "));
        let st = d.lock();
        assert_eq!(st.active[0].label.len(), MAX_LABEL_BYTES);
    }

    #[test]
    fn label_with_spaces_preserved() {
        let d = test_daemon(1 << 30);
        let reply = d.handle_line("RESERVE 4096 1234 my crate v2");
        assert!(reply.starts_with("GRANTED "));
        assert_eq!(d.lock().active[0].label, "my crate v2");
    }

    /// End-to-end over a real UnixListener: bind, serve in a thread, drive the
    /// client `status_at`/`ping` against it.
    #[test]
    fn end_to_end_socket_status_and_ping() {
        let fixture = TestSocket::new("end-to-end");
        let listener = UnixListener::bind(&fixture.path).expect("bind");
        make_socket_private(&fixture.path);
        let daemon = test_daemon(8 << 30);
        // Grant one reservation directly so STATUS has content. Use the live pid
        // so the snapshot describes an active worker.
        let _ = daemon.handle_line(&format!("RESERVE 4096 {} alpha", std::process::id()));
        // Serve two connections (PING + STATUS) in a background thread.
        let d2 = Arc::clone(&daemon);
        let handle = thread::spawn(move || {
            for stream in listener.incoming().take(2) {
                if let Ok(s) = stream {
                    d2.serve_conn(s);
                }
            }
        });
        // PING and STATUS over the wire.
        assert!(ping_at(&fixture.path), "daemon answers PING");
        let status = status_at(&fixture.path).expect("status over socket");
        assert_eq!(status.version, STATUS_VERSION);
        assert_eq!(status.reserved_bytes, 4096);
        assert_eq!(status.active.len(), 1);
        let _ = handle.join();
    }

    #[test]
    fn explicit_endpoint_reserve_helper_is_active_and_releases() {
        // Both ambient inputs are supplied by the test rather than observed:
        // the client budget is a constant (so no process-global cache sits
        // between the daemon's advertised ceiling and the client's acceptance
        // check), and the observational deadline is the test's own (so the
        // assertion is about RESERVE/RELEASE framing, not about how quickly
        // this host scheduled the responder below).
        let fixture = TestSocket::new("explicit-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind explicit reserve server");
        make_socket_private(&fixture.path);
        let daemon = test_daemon(64 << 10);
        let observed = Arc::clone(&daemon);
        let server = spawn_ready_responder(move || {
            let (stream, _) = listener.accept().expect("accept explicit reserve client");
            daemon.serve_conn(stream);
        });

        let reservation = reserve_labeled_at_with(
            &fixture.path,
            4096,
            "release-proof",
            TEST_OBSERVER_TIMEOUT,
            || TEST_CLIENT_BUDGET,
        )
        .expect("daemon reply");
        assert!(reservation.is_active());
        assert_eq!(reservation.bytes(), 4096);
        assert_eq!(observed.lock().reserved_bytes, 4096);
        release(reservation);
        server.join().expect("explicit reserve server joined");
        assert_eq!(observed.lock().reserved_bytes, 0);
    }

    /// True once a connect to `path` fails: no descriptor anywhere still holds
    /// the listener that was published there.
    ///
    /// Dropping the owner closes THIS process's descriptor, but the test binary
    /// runs other tests that spawn children meanwhile, some by fork and exec
    /// (`inherit_fd_across_exec` installs a `pre_exec` hook). A forked child
    /// holds a copy of every descriptor until it execs, and one forked between
    /// std's `socket()` and its `FIOCLEX` keeps the copy until it exits, so the
    /// endpoint can still accept for a moment after its owner has gone. That
    /// failed this test once in a push-lane run (2026-10-01, load average about
    /// 120) and passed alone 20 of 20 times. The deadline is a hang detector,
    /// not a latency budget: a listener that never closes still fails.
    fn listener_gone_within_hang_detector(path: &Path) -> bool {
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if UnixStream::connect(path).is_err() {
                return true;
            }
            if Instant::now() >= deadline {
                return false;
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn owned_socket_is_private_singleton_and_leaves_stale_endpoint() {
        use std::os::unix::fs::PermissionsExt as _;

        let fixture = TestSocket::new("owned");
        let owned = bind_owned_socket(&fixture.path).expect("first owner binds");
        let identity = owned.identity;
        let metadata = std::fs::symlink_metadata(&fixture.path).expect("socket metadata");
        assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
        assert_eq!(socket_identity_at(&fixture.path).expect("identity"), Some(identity));

        let error = bind_owned_socket(&fixture.path).err().expect("second owner refused");
        assert_eq!(error.kind(), std::io::ErrorKind::AddrInUse);
        assert_eq!(socket_identity_at(&fixture.path).expect("identity"), Some(identity));
        UnixStream::connect(&fixture.path).expect("first owner's socket remains reachable");

        owned.mark_clean().expect("fixture proves a quiescent clean shutdown");
        drop(owned);
        assert!(fixture.path.exists(), "normal drop deliberately leaves a stale socket");
        assert!(listener_gone_within_hang_detector(&fixture.path), "stale socket has no listener");

        let restarted =
            bind_owned_socket(&fixture.path).expect("next lock owner reclaims stale socket");
        assert!(UnixStream::connect(&fixture.path).is_ok(), "restart publishes a live endpoint");
        assert_eq!(
            socket_identity_at(&fixture.path).expect("restart identity"),
            Some(restarted.identity)
        );
        restarted.mark_clean().expect("leave fixture epoch clean");
    }

    #[test]
    fn private_socket_is_private_before_atomic_publication_without_umask() {
        let fixture = TestSocket::new("private-publication");
        let parent = fixture.path.parent().expect("fixture parent");
        let stage = stage_private_socket(parent).expect("stage private socket");

        assert!(!fixture.path.exists(), "the rendezvous path is absent before publication");
        let directory_metadata =
            std::fs::symlink_metadata(&stage.directory).expect("staging directory metadata");
        assert!(directory_metadata.file_type().is_dir());
        assert_eq!(directory_metadata.permissions().mode() & 0o777, 0o700);
        let socket_metadata =
            std::fs::symlink_metadata(&stage.socket).expect("staged socket metadata");
        assert!(socket_metadata.file_type().is_socket());
        assert_eq!(socket_metadata.permissions().mode() & 0o777, 0o600);

        let listener = stage.publish(&fixture.path).expect("publish staged socket");
        let published =
            std::fs::symlink_metadata(&fixture.path).expect("published socket metadata");
        assert!(published.file_type().is_socket());
        assert_eq!(published.permissions().mode() & 0o777, 0o600);
        UnixStream::connect(&fixture.path).expect("published listener is reachable");
        drop(listener);
    }

    #[test]
    fn an_explicit_runtime_directory_must_be_private_and_absolute() {
        let fixture = TestSocket::new("explicit-runtime-dir");
        let dir = fixture.path.parent().expect("fixture directory").to_path_buf();
        let socket = host_socket_path_in(&dir).expect("a private 0700 directory is accepted");
        assert_eq!(socket, std::fs::canonicalize(&dir).unwrap().join(HOST_SOCKET_NAME));
        assert_ne!(Some(socket), host_socket_path().ok(), "it is not the host endpoint");

        let relative = host_socket_path_in(Path::new("relative/dir")).unwrap_err();
        assert_eq!(relative.kind(), std::io::ErrorKind::InvalidInput);

        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755)).unwrap();
        let shared = host_socket_path_in(&dir).unwrap_err();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(shared.kind(), std::io::ErrorKind::PermissionDenied, "{shared}");

        let missing = host_socket_path_in(&dir.join("absent")).unwrap_err();
        assert_eq!(missing.kind(), std::io::ErrorKind::NotFound);
    }

    #[test]
    fn host_socket_path_is_stable_private_and_target_independent() {
        let first = host_socket_path().expect("resolve private host endpoint");
        let second = host_socket_path().expect("resolve the same host endpoint again");
        assert_eq!(first, second);
        assert_eq!(first.file_name(), Some(std::ffi::OsStr::new(HOST_SOCKET_NAME)));

        let expected_parent = std::fs::canonicalize("/tmp")
            .expect("canonical system temporary directory")
            .join(format!("{LOCK_ROOT_PREFIX}-{}", unsafe { libc::geteuid() }));
        assert_eq!(first.parent(), Some(expected_parent.as_path()));
        let metadata = std::fs::symlink_metadata(&expected_parent).expect("runtime root metadata");
        assert!(metadata.file_type().is_dir());
        assert_eq!(metadata.uid(), unsafe { libc::geteuid() });
        assert_eq!(metadata.permissions().mode() & 0o777, 0o700);

        let unrelated_target = TestSocket::new("different-cargo-target");
        assert_ne!(first.parent(), unrelated_target.path.parent());
    }

    #[test]
    fn target_cleanup_cannot_split_the_external_lock_domain() {
        let fixture = TestSocket::new("target-clean");
        let owner = bind_owned_socket(&fixture.path).expect("first owner binds");
        let stable_lock = owner.ownership_lock.path.clone();
        assert!(stable_lock.exists(), "stable sentinel exists");
        assert_ne!(
            stable_lock.parent(),
            fixture.path.parent(),
            "ownership sentinel is outside the Cargo-target-like directory"
        );
        let lock_metadata = std::fs::symlink_metadata(&stable_lock).expect("stable lock metadata");
        assert!(lock_metadata.file_type().is_file());
        assert_eq!(lock_metadata.uid(), unsafe { libc::geteuid() });
        assert_eq!(lock_metadata.permissions().mode() & 0o077, 0);

        // Simulate cargo clean deleting both the endpoint and the obsolete
        // in-target `<socket>.lock` sentinel while daemon A still owns the
        // external lock inode.
        std::fs::write(fixture.lock_path(), b"obsolete in-target lock")
            .expect("create obsolete lock fixture");
        std::fs::remove_file(&fixture.path).expect("remove live socket pathname");
        std::fs::remove_file(fixture.lock_path()).expect("remove obsolete lock");

        let error = bind_owned_socket(&fixture.path).err().expect("second authority refused");
        assert_eq!(error.kind(), std::io::ErrorKind::AddrInUse);
        assert!(stable_lock.exists(), "stable sentinel is never unlinked");

        owner.mark_clean().expect("fixture proves a quiescent clean shutdown");
        drop(owner);
        let restarted = bind_owned_socket(&fixture.path).expect("restart after owner exit");
        assert!(UnixStream::connect(&fixture.path).is_ok());
        restarted.mark_clean().expect("leave fixture epoch clean");
        drop(restarted);
        assert!(stable_lock.exists(), "sentinel survives clean restart");
    }

    #[test]
    fn dirty_epoch_refuses_automatic_restart_until_explicit_quiescence_recovery() {
        let fixture = TestSocket::new("dirty-epoch");
        let owner = prepare_owned_socket(&fixture.path, |_| Ok(()))
            .expect("first owner completes pre-admission initialization and marks DIRTY");
        drop(owner);

        let error = bind_owned_socket(&fixture.path)
            .err()
            .expect("an unclean prior owner must prevent automatic restart");
        assert_eq!(error.kind(), std::io::ErrorKind::Other);
        assert!(error.to_string().contains("automatic restart is refused"));

        assert!(
            recover_dirty_epoch_after_quiescence(&fixture.path)
                .expect("explicit quiescence recovery succeeds"),
            "DIRTY must transition to CLEAN"
        );
        assert!(
            !recover_dirty_epoch_after_quiescence(&fixture.path)
                .expect("clean recovery is idempotent"),
            "a second recovery observes CLEAN"
        );

        let restarted = bind_owned_socket(&fixture.path).expect("recovered epoch may restart");
        restarted.mark_clean().expect("leave fixture epoch clean");
    }

    #[test]
    fn failed_pre_admission_initialization_leaves_clean_restartable_epoch() {
        let fixture = TestSocket::new("pre-admission-failure");
        let error = prepare_owned_socket(&fixture.path, |_| {
            Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "injected pre-admission initialization failure",
            ))
        })
        .err()
        .expect("injected initialization must fail");
        assert!(error.to_string().contains("injected pre-admission"));

        let restarted = bind_owned_socket(&fixture.path)
            .expect("no request was admitted, so the CLEAN epoch restarts automatically");
        restarted.mark_clean().expect("leave fixture epoch clean");
    }

    #[test]
    fn torn_epoch_fails_closed_immediately() {
        let fixture = TestSocket::new("torn-epoch");
        let canonical = canonical_socket_path(&fixture.path).expect("canonical fixture socket");
        let (ownership, _) = open_stable_ownership_lock(&canonical).expect("create epoch sentinel");
        ownership.write_epoch(b"trustd.epoch.v1 torn").expect("write torn epoch fixture");
        drop(ownership);

        let started = Instant::now();
        let error = bind_owned_socket(&fixture.path)
            .err()
            .expect("a persistently torn epoch must prevent automatic restart");
        assert_eq!(error.kind(), std::io::ErrorKind::Other);
        assert!(error.to_string().contains("automatic restart is refused"));
        assert!(
            started.elapsed() < Duration::from_secs(1),
            "a torn epoch is refused without waiting"
        );

        assert!(
            recover_dirty_epoch_after_quiescence(&fixture.path)
                .expect("explicit recovery repairs the torn epoch")
        );
    }

    #[test]
    fn published_sentinel_is_clean_and_carries_no_staging_link() {
        let fixture = TestSocket::new("sentinel-publication");
        let canonical = canonical_socket_path(&fixture.path).expect("canonical fixture socket");
        let (ownership, epoch) =
            open_stable_ownership_lock(&canonical).expect("create epoch sentinel");
        assert_eq!(epoch, StableEpoch::Clean, "a sentinel is never published uninitialized");
        assert_eq!(
            std::fs::read(&ownership.path).expect("read published sentinel"),
            CLEAN_EPOCH_RECORD
        );
        let metadata = std::fs::symlink_metadata(&ownership.path).expect("sentinel metadata");
        assert_eq!(metadata.nlink(), 1, "the staging name is removed before ownership returns");
        let parent = ownership.path.parent().expect("sentinel parent");
        let prefix = ownership.path.file_name().expect("sentinel name").to_string_lossy();
        let prefix = format!("{prefix}.");
        let leftovers: Vec<_> = std::fs::read_dir(parent)
            .expect("list runtime root")
            .filter_map(|entry| entry.ok())
            .filter(|entry| entry.file_name().to_string_lossy().starts_with(&prefix))
            .collect();
        assert!(leftovers.is_empty(), "no staging sentinel is left behind: {leftovers:?}");
    }

    /// UNSAFE twin of moving the link-count check behind the lock: a contender
    /// may report `AddrInUse` for a locked multiply-linked sentinel (that is the
    /// creator's publication instant), but once the lock is free such a
    /// sentinel must still be refused — never owned, never written.
    #[test]
    fn multiply_linked_sentinel_is_never_owned() {
        let fixture = TestSocket::new("sentinel-extra-link");
        let canonical = canonical_socket_path(&fixture.path).expect("canonical fixture socket");
        let (ownership, _) = open_stable_ownership_lock(&canonical).expect("create epoch sentinel");
        let sentinel = ownership.path.clone();
        let mut alias = sentinel.as_os_str().to_owned();
        alias.push(".alias");
        let alias = std::path::PathBuf::from(alias);
        std::fs::hard_link(&sentinel, &alias).expect("add a second link to the sentinel");

        let contended = open_stable_ownership_lock(&canonical)
            .err()
            .expect("a locked sentinel is never shared");
        assert_eq!(contended.kind(), std::io::ErrorKind::AddrInUse);
        drop(ownership);

        let refused = open_stable_ownership_lock(&canonical)
            .err()
            .expect("an unlocked multiply-linked sentinel is refused");
        assert_eq!(refused.kind(), std::io::ErrorKind::PermissionDenied);
        let bind_error =
            bind_owned_socket(&fixture.path).err().expect("binding refuses the aliased sentinel");
        assert_eq!(bind_error.kind(), std::io::ErrorKind::PermissionDenied);
        assert_eq!(
            std::fs::read(&alias).expect("read aliased sentinel"),
            CLEAN_EPOCH_RECORD,
            "a refused sentinel is never written"
        );
        std::fs::remove_file(&alias).expect("remove sentinel alias");
    }

    /// A pid that has exited and been reaped, so `kill(pid, 0)` reports ESRCH.
    fn exited_pid() -> u32 {
        for _ in 0..32 {
            let mut child = std::process::Command::new("/usr/bin/true")
                .spawn()
                .expect("spawn a short-lived child");
            let pid = child.id();
            child.wait().expect("reap the short-lived child");
            if !process_may_be_alive(pid) {
                return pid;
            }
        }
        panic!("could not obtain an exited pid")
    }

    /// The staging name a creator with `pid` uses for `sentinel`, spelled out
    /// independently of the production formatter so the pattern is pinned.
    fn staging_path_for(sentinel: &Path, pid: u32, nonce: &str, sequence: &str) -> PathBuf {
        let mut staged = sentinel.as_os_str().to_owned();
        staged.push(format!(".{pid:x}-{nonce}-{sequence}.new"));
        PathBuf::from(staged)
    }

    /// Publish a sentinel with `record`, then leave it exactly as a creator that
    /// died between `link(2)` and unlinking its staging name leaves it: a second
    /// link named `<sentinel>.<pid>-<nonce>-<seq>.new` in the runtime root.
    fn sentinel_with_staging_link(
        fixture: &TestSocket,
        record: &[u8],
        creator: u32,
    ) -> (PathBuf, PathBuf) {
        let canonical = canonical_socket_path(&fixture.path).expect("canonical fixture socket");
        let (ownership, _) = open_stable_ownership_lock(&canonical).expect("create epoch sentinel");
        ownership.write_epoch(record).expect("write epoch fixture");
        let sentinel = ownership.path.clone();
        let staged = staging_path_for(&sentinel, creator, "17a2b3c4d5e6f", "3");
        std::fs::hard_link(&sentinel, &staged).expect("leave the creator's staging link");
        drop(ownership);
        assert_eq!(std::fs::symlink_metadata(&sentinel).expect("sentinel").nlink(), 2);
        (sentinel, staged)
    }

    #[test]
    fn staging_name_pattern_is_exact() {
        let name = std::ffi::OsStr::new("ab12.lock");
        let staged = staged_sentinel_name(name, 0x1f2, 0xdead, 0);
        assert_eq!(staged, std::ffi::OsStr::new("ab12.lock.1f2-dead-0.new"));
        assert_eq!(staged_sentinel_creator(name, &staged), Some(0x1f2));
        for foreign in [
            "ab12.lock",
            "ab12.lock.alias",
            "ab12.lock.1f2-dead-0.new.bak",
            "ab12.lock.1f2-dead.new",
            "ab12.lock.1f2-dead-0-1.new",
            "ab12.lock.1F2-dead-0.new",
            "ab12.lock.01f2-dead-0.new",
            "ab12.lock.0-dead-0.new",
            "ab12.lock.-dead-0.new",
            "ab12.lock.ffffffff-dead-0.new",
            "ab12.lock.100000000-dead-0.new",
            "ab12.lockx.1f2-dead-0.new",
            "cd34.lock.1f2-dead-0.new",
            "ab12.lock1f2-dead-0.new",
        ] {
            assert_eq!(
                staged_sentinel_creator(name, std::ffi::OsStr::new(foreign)),
                None,
                "{foreign} is not a staging name of ab12.lock"
            );
        }
    }

    /// The crash window the locked-and-CLEAN publication opens: the creator died
    /// between `link(2)` and removing its staging name. Both the ordinary bind
    /// and the operator's crash recovery must clear that leftover.
    #[test]
    fn sentinel_left_with_dead_creator_staging_link_is_recovered_by_both_paths() {
        let bind_fixture = TestSocket::new("dead-stage-bind");
        let (sentinel, staged) =
            sentinel_with_staging_link(&bind_fixture, CLEAN_EPOCH_RECORD, exited_pid());
        let owned = bind_owned_socket(&bind_fixture.path)
            .expect("an exited creator's staging link does not block the next owner");
        assert!(!staged.exists(), "the dead creator's staging link is removed");
        assert_eq!(std::fs::symlink_metadata(&sentinel).expect("sentinel").nlink(), 1);
        assert_eq!(owned.ownership_lock.path, sentinel);
        owned.mark_clean().expect("leave fixture epoch clean");
        drop(owned);

        let clean_fixture = TestSocket::new("dead-stage-recover-clean");
        let (sentinel, staged) =
            sentinel_with_staging_link(&clean_fixture, CLEAN_EPOCH_RECORD, exited_pid());
        assert!(
            !recover_dirty_epoch_after_quiescence(&clean_fixture.path)
                .expect("crash recovery clears the dead creator's staging link"),
            "the creator's record was CLEAN"
        );
        assert!(!staged.exists());
        assert_eq!(std::fs::symlink_metadata(&sentinel).expect("sentinel").nlink(), 1);

        let dirty_fixture = TestSocket::new("dead-stage-recover-dirty");
        let (sentinel, staged) =
            sentinel_with_staging_link(&dirty_fixture, DIRTY_EPOCH_RECORD, exited_pid());
        let refused = bind_owned_socket(&dirty_fixture.path)
            .err()
            .expect("the epoch is still classified after the link is cleared");
        assert_eq!(refused.kind(), std::io::ErrorKind::Other);
        assert!(refused.to_string().contains("automatic restart is refused"), "{refused}");
        assert!(!staged.exists());
        assert!(
            recover_dirty_epoch_after_quiescence(&dirty_fixture.path)
                .expect("explicit recovery repairs the DIRTY epoch"),
        );
        assert_eq!(std::fs::read(&sentinel).expect("sentinel record"), CLEAN_EPOCH_RECORD);
        let restarted = bind_owned_socket(&dirty_fixture.path).expect("recovered epoch restarts");
        restarted.mark_clean().expect("leave fixture epoch clean");
    }

    /// UNSAFE twin: a staging link whose creator is still running is refused by
    /// both paths, names the fix, and is left untouched; once the creator exits
    /// the same state recovers.
    #[test]
    fn live_creator_staging_link_still_refuses() {
        let fixture = TestSocket::new("live-stage");
        let creator = TestChild(
            std::process::Command::new("/bin/sleep")
                .arg("600")
                .stdin(std::process::Stdio::null())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .expect("spawn a live creator stand-in"),
        );
        let (sentinel, staged) =
            sentinel_with_staging_link(&fixture, CLEAN_EPOCH_RECORD, creator.0.id());

        let bind_error =
            bind_owned_socket(&fixture.path).err().expect("live creator: bind refused");
        let recover_error = recover_dirty_epoch_after_quiescence(&fixture.path)
            .err()
            .expect("live creator: recovery refused");
        for error in [&bind_error, &recover_error] {
            assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied, "{error}");
            let message = error.to_string();
            assert!(message.contains(&staged.display().to_string()), "{message}");
            assert!(message.contains(&format!("pid {}", creator.0.id())), "{message}");
            assert!(message.contains("still running"), "{message}");
            assert!(message.contains("delete only"), "{message}");
        }
        assert!(staged.exists(), "a live creator's staging link is never removed");
        assert_eq!(std::fs::symlink_metadata(&sentinel).expect("sentinel").nlink(), 2);

        // Our own (live) pid is refused the same way.
        let own = staging_path_for(&sentinel, std::process::id(), "1", "0");
        std::fs::rename(&staged, &own).expect("rename the staging link to our own pid");
        let own_error = bind_owned_socket(&fixture.path).err().expect("own pid: bind refused");
        assert_eq!(own_error.kind(), std::io::ErrorKind::PermissionDenied);
        assert!(own.exists());
        std::fs::rename(&own, &staged).expect("restore the creator's staging link");

        drop(creator);
        let owned = bind_owned_socket(&fixture.path).expect("the exited creator's link is cleared");
        assert!(!staged.exists());
        owned.mark_clean().expect("leave fixture epoch clean");
    }

    /// UNSAFE twin: an extra link that is not a dead creator's staging name of
    /// this very inode in this very root is foreign, and stays refused.
    #[test]
    fn foreign_second_links_still_refuse() {
        let dead = exited_pid();
        let assert_refused = |fixture: &TestSocket, sentinel: &Path, what: &str| {
            for error in [
                bind_owned_socket(&fixture.path).err().expect("bind refuses a foreign link"),
                recover_dirty_epoch_after_quiescence(&fixture.path)
                    .err()
                    .expect("recovery refuses a foreign link"),
            ] {
                assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied, "{what}: {error}");
                let message = error.to_string();
                assert!(message.contains("-xdev -inum"), "{what}: {message}");
                assert!(message.contains("Never delete the sentinel"), "{what}: {message}");
            }
            assert_eq!(std::fs::symlink_metadata(sentinel).expect("sentinel").nlink(), 2, "{what}");
            assert_eq!(std::fs::read(sentinel).expect("record"), CLEAN_EPOCH_RECORD, "{what}");
        };

        // Not a staging name (each differs from the exact pattern).
        for (index, suffix) in [
            ".alias".to_string(),
            format!(".{dead:x}-1f-0.new.bak"),
            format!(".{dead:X}-1F-0.new"),
            format!(".0{dead:x}-1f-0.new"),
            format!(".{dead:x}-1f.new"),
            format!("x.{dead:x}-1f-0.new"),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = TestSocket::new(&format!("foreign-name-{index}"));
            let canonical = canonical_socket_path(&fixture.path).expect("canonical");
            let (ownership, _) = open_stable_ownership_lock(&canonical).expect("create sentinel");
            let sentinel = ownership.path.clone();
            drop(ownership);
            let mut alias = sentinel.as_os_str().to_owned();
            alias.push(&suffix);
            let alias = PathBuf::from(alias);
            std::fs::hard_link(&sentinel, &alias).expect("add a foreign-named link");
            assert_refused(&fixture, &sentinel, &suffix);
            assert!(alias.exists(), "{suffix}: a foreign link is never removed");
            std::fs::remove_file(&alias).expect("remove foreign link");
        }

        // A dead creator's staging name, but for ANOTHER inode; the sentinel's
        // own extra link lives elsewhere.
        let other_inode = TestSocket::new("foreign-inode");
        let canonical = canonical_socket_path(&other_inode.path).expect("canonical");
        let (ownership, _) = open_stable_ownership_lock(&canonical).expect("create sentinel");
        let sentinel = ownership.path.clone();
        drop(ownership);
        let fixture_dir = other_inode.path.parent().expect("fixture dir").to_path_buf();
        let alias = fixture_dir.join("sentinel-alias");
        std::fs::hard_link(&sentinel, &alias).expect("alias the sentinel outside the root");
        let foreign = fixture_dir.join("foreign-record");
        std::fs::write(&foreign, b"foreign data").expect("write a foreign file");
        let staged = staging_path_for(&sentinel, dead, "2e", "0");
        std::fs::hard_link(&foreign, &staged).expect("stage-named link to another inode");
        assert_refused(&other_inode, &sentinel, "another inode");
        assert_eq!(std::fs::read(&staged).expect("foreign staging"), b"foreign data");
        for path in [&alias, &foreign, &staged] {
            std::fs::remove_file(path).expect("remove fixture link");
        }

        // A dead creator's staging name of the SAME inode, but in another root.
        let other_root = TestSocket::new("foreign-root");
        let canonical = canonical_socket_path(&other_root.path).expect("canonical");
        let (ownership, _) = open_stable_ownership_lock(&canonical).expect("create sentinel");
        let sentinel = ownership.path.clone();
        drop(ownership);
        let elsewhere = other_root.path.parent().expect("fixture dir").join(staged_sentinel_name(
            sentinel.file_name().expect("sentinel name"),
            dead,
            0x3d,
            0,
        ));
        std::fs::hard_link(&sentinel, &elsewhere).expect("stage-named link in another directory");
        assert_refused(&other_root, &sentinel, "another root");
        assert!(elsewhere.exists(), "a link outside the runtime root is never removed");
        std::fs::remove_file(&elsewhere).expect("remove fixture link");
    }

    /// Staging files a creator left by dying BEFORE publication are removed by
    /// the next lock holder — both when it creates the sentinel and when it
    /// opens an existing one — while live-creator and multiply-linked staging
    /// files are kept.
    #[test]
    fn orphaned_dead_creator_staging_files_are_removed() {
        let dead = exited_pid();
        let fixture = TestSocket::new("orphan-stage");
        let sentinel = stable_lock_path_for_socket(
            &canonical_socket_path(&fixture.path).expect("canonical fixture socket"),
        )
        .expect("sentinel path");
        assert!(!sentinel.exists(), "fresh fixture has no sentinel yet");
        let fixture_dir = fixture.path.parent().expect("fixture dir").to_path_buf();

        let orphan_before_create = staging_path_for(&sentinel, dead, "4a", "0");
        std::fs::write(&orphan_before_create, CLEAN_EPOCH_RECORD).expect("orphan fixture");
        std::fs::set_permissions(&orphan_before_create, std::fs::Permissions::from_mode(0o600))
            .expect("private orphan");
        let owned = bind_owned_socket(&fixture.path).expect("create the sentinel");
        assert!(!orphan_before_create.exists(), "the creating owner removes a dead orphan");
        owned.mark_clean().expect("leave fixture epoch clean");
        drop(owned);

        let orphan = staging_path_for(&sentinel, dead, "4b", "1");
        let live = staging_path_for(&sentinel, std::process::id(), "4c", "2");
        let shared = staging_path_for(&sentinel, dead, "4d", "3");
        let shared_target = fixture_dir.join("shared-target");
        let mut unrelated = sentinel.as_os_str().to_owned();
        unrelated.push(format!("x.{dead:x}-4e-4.new"));
        let unrelated = PathBuf::from(unrelated);
        for path in [&orphan, &live, &unrelated, &shared_target] {
            std::fs::write(path, b"staged").expect("staging fixture");
        }
        std::fs::hard_link(&shared_target, &shared).expect("multiply-linked staging fixture");

        let owned = bind_owned_socket(&fixture.path).expect("open the existing sentinel");
        assert!(!orphan.exists(), "a dead creator's orphan is removed");
        assert!(live.exists(), "a live creator's staging file is kept");
        assert!(shared.exists(), "a multiply-linked staging name is kept");
        assert!(unrelated.exists(), "another sentinel's name is kept");
        owned.mark_clean().expect("leave fixture epoch clean");
        drop(owned);
        for path in [&live, &shared, &unrelated, &shared_target] {
            std::fs::remove_file(path).expect("remove fixture");
        }
    }

    #[test]
    fn socket_parent_and_endpoint_trust_boundaries_fail_closed() {
        let parent_fixture = TestSocket::new("untrusted-parent");
        let parent = parent_fixture.path.parent().expect("fixture parent");
        std::fs::set_permissions(parent, std::fs::Permissions::from_mode(0o770))
            .expect("make parent group-writable");
        let error =
            bind_owned_socket(&parent_fixture.path).err().expect("group-writable parent refused");
        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        std::fs::set_permissions(parent, std::fs::Permissions::from_mode(0o700))
            .expect("restore parent mode for cleanup");

        let endpoint_fixture = TestSocket::new("untrusted-endpoint");
        let endpoint = UnixListener::bind(&endpoint_fixture.path).expect("bind endpoint fixture");
        std::fs::set_permissions(&endpoint_fixture.path, std::fs::Permissions::from_mode(0o666))
            .expect("make endpoint public");
        assert!(status_at(&endpoint_fixture.path).is_none(), "public endpoint is never reused");
        drop(endpoint);
    }

    #[test]
    fn socket_authority_rejects_writable_ancestor_above_private_parent() {
        let fixture = TestSocket::new("writable-socket-ancestor");
        let root = fixture.path.parent().expect("fixture parent");
        let shared = root.join("shared");
        let private_parent = shared.join("private-endpoint");
        std::fs::create_dir(&shared).expect("create shared ancestor");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o700))
            .expect("make construction ancestor private");
        std::fs::create_dir(&private_parent).expect("create private immediate parent");
        std::fs::set_permissions(&private_parent, std::fs::Permissions::from_mode(0o700))
            .expect("make immediate parent private");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o777))
            .expect("make ancestor cross-user writable");

        let socket = private_parent.join("daemon.sock");
        let error = canonical_socket_path(&socket)
            .expect_err("a private immediate parent cannot hide a writable ancestor");

        std::fs::remove_dir(&private_parent).expect("remove private endpoint parent");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o700))
            .expect("restore shared ancestor for cleanup");
        std::fs::remove_dir(&shared).expect("remove shared ancestor");

        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        assert!(
            error.to_string().contains("trustd socket ancestor"),
            "diagnostic names the complete socket authority chain: {error}"
        );
    }

    #[test]
    fn concurrent_binders_leave_exactly_one_stable_owner() {
        // No budget injection here, deliberately. `bind_owned_socket` and its
        // whole call graph — canonical_socket_path, try_stable_ownership_lock,
        // open_stable_ownership_lock, create_locked_clean_sentinel,
        // reconcile_sentinel_links, socket_identity_at, connect_unix_until,
        // bind_private_socket — never read `machine_budget_bytes()`, so this
        // test exercises no admission and an injection buys it nothing. It is
        // not free, though: `TestTotalMemory` zeroes the process-global budget
        // cache on entry and restores a value captured BEFORE this test's
        // unbounded wait (two spawns, a 3-way barrier, two blocking recvs, two
        // joins), clobbering any budget a concurrently running test legitimately
        // computed inside that window — and it would hold the process-wide
        // ENV_TEST_LOCK across that same wait, serialising every
        // budget-sensitive test in the crate behind socket and filesystem work.
        // If the bind path ever becomes budget-dependent, the injection returns
        // with a critical section that ends before the barrier.
        let fixture = TestSocket::new("concurrent");
        let start = Arc::new(std::sync::Barrier::new(3));
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        let mut release_senders = Vec::new();
        let mut handles = Vec::new();

        for _ in 0..2 {
            let sock = fixture.path.clone();
            let start = Arc::clone(&start);
            let result_tx = result_tx.clone();
            let (release_tx, release_rx) = std::sync::mpsc::channel();
            release_senders.push(release_tx);
            handles.push(thread::spawn(move || {
                start.wait();
                match bind_owned_socket(&sock) {
                    Ok(owned) => {
                        result_tx.send(Ok(owned.identity)).expect("report winner");
                        let _ = release_rx.recv();
                        drop(owned);
                    }
                    Err(error) => {
                        result_tx.send(Err(error.kind())).expect("report loser");
                    }
                }
            }));
        }
        drop(result_tx);
        start.wait();

        let outcomes = [
            result_rx.recv().expect("first bind outcome"),
            result_rx.recv().expect("second bind outcome"),
        ];
        let winners: Vec<_> = outcomes.iter().filter_map(|result| result.as_ref().ok()).collect();
        assert_eq!(winners.len(), 1, "exactly one concurrent binder wins: {outcomes:?}");
        assert!(
            outcomes.iter().any(|result| matches!(result, Err(std::io::ErrorKind::AddrInUse))),
            "the losing binder observes stable ownership: {outcomes:?}"
        );
        assert_eq!(socket_identity_at(&fixture.path).expect("winner identity"), Some(*winners[0]));
        UnixStream::connect(&fixture.path).expect("winner remains reachable");

        for release in release_senders {
            let _ = release.send(());
        }
        for handle in handles {
            handle.join().expect("binder thread joined");
        }
    }

    /// The creation race behind the intermittent `[Err(AddrInUse), Err(Other)]`:
    /// a peer that opened a brand-new sentinel and took its flock before the
    /// creator did read an uninitialized record, and the creator then lost its
    /// own flock and gave up, so NOBODY owned the endpoint. Every round races
    /// several binders on a FRESH sentinel — the only state with that window.
    #[test]
    fn fresh_sentinel_contention_always_yields_exactly_one_owner() {
        const ROUNDS: usize = 64;
        const BINDERS: usize = 8;
        for round in 0..ROUNDS {
            let fixture = TestSocket::new("fresh-contention");
            let start = Arc::new(std::sync::Barrier::new(BINDERS));
            let handles: Vec<_> = (0..BINDERS)
                .map(|_| {
                    let sock = fixture.path.clone();
                    let start = Arc::clone(&start);
                    thread::spawn(move || {
                        start.wait();
                        bind_owned_socket(&sock)
                    })
                })
                .collect();
            let outcomes: Vec<_> =
                handles.into_iter().map(|h| h.join().expect("binder thread joined")).collect();
            let kinds: Vec<_> =
                outcomes.iter().map(|o| o.as_ref().map(|_| ()).map_err(|e| e.kind())).collect();
            assert_eq!(
                outcomes.iter().filter(|o| o.is_ok()).count(),
                1,
                "round {round}: exactly one fresh-sentinel binder owns the endpoint: {kinds:?}"
            );
            for outcome in &outcomes {
                if let Err(error) = outcome {
                    assert_eq!(
                        error.kind(),
                        std::io::ErrorKind::AddrInUse,
                        "round {round}: every loser observes the live owner: {error}"
                    );
                }
            }
            for owned in outcomes.into_iter().flatten() {
                owned.mark_clean().expect("leave fixture epoch clean");
            }
        }
    }

    #[test]
    fn stale_socket_is_reclaimed_but_live_socket_is_never_replaced() {
        let stale_fixture = TestSocket::new("stale");
        let stale = UnixListener::bind(&stale_fixture.path).expect("bind stale socket");
        make_socket_private(&stale_fixture.path);
        drop(stale);
        assert!(stale_fixture.path.exists(), "dropped listener leaves stale path");
        let owner = bind_owned_socket(&stale_fixture.path).expect("reclaim stale socket");
        UnixStream::connect(&stale_fixture.path).expect("reclaimed socket reachable");
        drop(owner);

        let live_fixture = TestSocket::new("legacy-live");
        let live = UnixListener::bind(&live_fixture.path).expect("bind live legacy socket");
        make_socket_private(&live_fixture.path);
        let before = socket_identity_at(&live_fixture.path).expect("live identity");
        let error = bind_owned_socket(&live_fixture.path).err().expect("live socket refused");
        assert_eq!(error.kind(), std::io::ErrorKind::AddrInUse);
        assert_eq!(socket_identity_at(&live_fixture.path).expect("live identity"), before);
        drop(live);
    }

    #[test]
    fn socket_owner_refuses_non_socket_paths_and_preserves_replacements() {
        use std::os::unix::fs::symlink;

        let regular_fixture = TestSocket::new("regular");
        std::fs::write(&regular_fixture.path, b"do not delete").expect("write regular fixture");
        let error = bind_owned_socket(&regular_fixture.path).err().expect("regular file refused");
        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        assert_eq!(
            std::fs::read(&regular_fixture.path).expect("regular file preserved"),
            b"do not delete"
        );

        let symlink_fixture = TestSocket::new("symlink");
        let target = symlink_fixture.path.parent().expect("fixture parent").join("target");
        std::fs::write(&target, b"target").expect("write symlink target");
        symlink(&target, &symlink_fixture.path).expect("create socket-path symlink");
        let error = bind_owned_socket(&symlink_fixture.path).err().expect("symlink refused");
        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        assert_eq!(std::fs::read(&target).expect("symlink target preserved"), b"target");
        let _ = std::fs::remove_file(target);

        let replaced_fixture = TestSocket::new("replacement");
        let owner = bind_owned_socket(&replaced_fixture.path).expect("bind original socket");
        std::fs::remove_file(&replaced_fixture.path).expect("unlink original socket path");
        std::fs::write(&replaced_fixture.path, b"new owner").expect("install replacement");
        drop(owner);
        assert_eq!(
            std::fs::read(&replaced_fixture.path).expect("replacement preserved"),
            b"new owner"
        );
    }

    #[test]
    fn trustd_resolution_is_sibling_only_and_fails_closed() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let fixture = TestSocket::new("resolution");
        let parent = fixture.path.parent().expect("fixture parent");
        let executable = parent.join("targo");
        let sibling = parent.join(format!("trustd{}", std::env::consts::EXE_SUFFIX));
        std::fs::write(&executable, b"tool").expect("write executable fixture");

        assert_eq!(resolve_trustd_sibling(&executable), None, "absent sibling fails closed");

        std::fs::write(&sibling, b"daemon").expect("write sibling fixture");
        std::fs::set_permissions(&sibling, std::fs::Permissions::from_mode(0o600))
            .expect("make sibling non-executable");
        assert_eq!(
            resolve_trustd_sibling(&executable),
            None,
            "non-executable sibling fails closed"
        );

        std::fs::set_permissions(&sibling, std::fs::Permissions::from_mode(0o700))
            .expect("make sibling executable");
        assert_eq!(resolve_trustd_sibling(&executable), Some(sibling.clone()));

        std::fs::remove_file(&sibling).expect("remove sibling fixture");
        let redirected = parent.join("ambient-trustd");
        std::fs::write(&redirected, b"ambient").expect("write redirected target");
        std::fs::set_permissions(&redirected, std::fs::Permissions::from_mode(0o700))
            .expect("make redirected target executable");
        symlink(&redirected, &sibling).expect("redirect sibling with symlink");
        assert_eq!(resolve_trustd_sibling(&executable), None, "symlink redirect fails closed");

        std::fs::remove_file(sibling).expect("remove sibling symlink");
        std::fs::remove_file(redirected).expect("remove redirected target");
        std::fs::remove_file(executable).expect("remove executable fixture");
    }

    fn spawn_readiness_fixture(script: &str) -> (std::process::Child, thread::JoinHandle<String>) {
        let mut child = std::process::Command::new("/bin/sh")
            .args(["-c", script])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("spawn readiness fixture");
        let stderr = child.stderr.take().expect("fixture stderr is piped");
        (child, capture_spawned_stderr(stderr))
    }

    /// [`wait_for_spawned_daemon`] with `window` for a lost race and an owner
    /// whose lock is never seen released.
    fn wait_with_held_lock<F, T>(
        child: std::process::Child,
        stderr: thread::JoinHandle<String>,
        timeout: Duration,
        window: Duration,
        is_ready: F,
    ) -> Result<T, EnsureDaemonError>
    where
        F: FnMut(Instant) -> Result<T, ProbeMiss>,
    {
        let mut held = || false;
        let lost_race = LostRaceWait { window, owner_released: &mut held };
        match wait_for_spawned_daemon(
            child,
            stderr,
            Path::new("/fixture/trustd"),
            timeout,
            lost_race,
            is_ready,
        )? {
            SpawnedDaemon::Ready(ready) => Ok(ready),
            SpawnedDaemon::OwnerVanished { .. } => panic!("a lock that is held never vanishes"),
        }
    }

    /// Every probe a lost-race wait made: when it was made, and the deadline
    /// it was given. [`wait_for_spawned_daemon`] bounds each probe of the
    /// running child by its readiness deadline, set `timeout` after it started
    /// and so at most `timeout` after the first probe. It hands the post-exit
    /// wait ([`wait_for_live_owner`]) a deadline `window` after the exit, so at
    /// least `window` after the first probe. With `window > timeout`, a
    /// deadline more than `timeout` after the first probe marks a post-exit
    /// try, under any load.
    #[derive(Default)]
    struct ProbeLog(Vec<(Instant, Instant)>);

    impl ProbeLog {
        fn record(&mut self, deadline: Instant) {
            self.0.push((Instant::now(), deadline));
        }

        /// Assert that the post-exit wait ran out one window
        /// (TRUSTD-LOST-RACE-1 and -2):
        /// * once the child exited, every try was a post-exit try, and every
        ///   one shared a single deadline, never moved by what a try answered;
        /// * that deadline is `window` after the exit: no earlier than `window`
        ///   after the first probe, and no later than `window` after the first
        ///   post-exit try;
        /// * the wait asked again, but slept between tries: a wait that sleeps
        ///   [`SPAWN_POLL_INTERVAL`] (or what remains, which ends it) between
        ///   tries makes at most `window / SPAWN_POLL_INTERVAL + 2`, since
        ///   `thread::sleep` never returns early;
        /// * it ended at the deadline: not before it, and less than `late`
        ///   after it (no grace and no second window follows).
        fn assert_one_window(
            &self,
            timeout: Duration,
            window: Duration,
            ended: Instant,
            late: Duration,
        ) {
            assert!(
                window > timeout,
                "a post-exit deadline is told apart only if window > timeout"
            );
            let (first, _) = *self.0.first().expect("the wait probed");
            let running_bound = first + timeout;
            let exited = self
                .0
                .iter()
                .position(|&(_, deadline)| deadline > running_bound)
                .expect("the post-exit wait probed");
            let post = &self.0[exited..];
            let (first_post, deadline) = post[0];
            assert!(
                post.iter().all(|&(_, later)| later > running_bound),
                "no probe of the running child after its exit: {} probes, the first post-exit at {exited}",
                self.0.len()
            );
            let moved = post.iter().filter(|&&(_, later)| later != deadline).count();
            assert_eq!(
                moved,
                0,
                "every post-exit try shares one deadline: {moved} of {} moved",
                post.len()
            );
            assert!(deadline >= first + window, "the deadline is a full window after the exit");
            assert!(deadline <= first_post + window, "the deadline is one window, set at the exit");
            let tries = post.len();
            let most = usize::try_from(window.as_millis() / SPAWN_POLL_INTERVAL.as_millis())
                .expect("a test window fits")
                + 2;
            assert!(tries > 2, "asked again: {tries} post-exit tries");
            assert!(tries <= most, "slept between tries: {tries} post-exit tries, at most {most}");
            assert!(
                ended >= deadline,
                "refused at the deadline, not before it: {:?} early",
                deadline.saturating_duration_since(ended)
            );
            assert!(
                ended < deadline + late,
                "refused at the deadline, not after it: {:?} late",
                ended.saturating_duration_since(deadline)
            );
        }
    }

    #[test]
    fn spawned_daemon_readiness_can_exceed_the_old_half_second_bound() {
        let (child, stderr) = spawn_readiness_fixture("sleep 1");
        let started = Instant::now();
        assert!(SPAWN_READY_TIMEOUT > Duration::from_millis(650));
        wait_with_held_lock(child, stderr, SPAWN_READY_TIMEOUT, LIVE_OWNER_ADOPT_TIMEOUT, |_| {
            (started.elapsed() >= Duration::from_millis(650))
                .then_some(())
                .ok_or(ProbeMiss::NotServing)
        })
        .expect("slow but bounded exact readiness must succeed");
        assert!(started.elapsed() >= Duration::from_millis(650));
    }

    #[test]
    fn spawned_daemon_early_exit_preserves_status_and_bounded_stderr() {
        let (child, stderr) = spawn_readiness_fixture(
            "printf 'startup-sentinel' >&2; printf '%20000s' x >&2; exit 23",
        );
        let error = wait_with_held_lock(
            child,
            stderr,
            Duration::from_secs(2),
            LIVE_OWNER_ADOPT_TIMEOUT,
            |_| Err::<(), _>(ProbeMiss::NotServing),
        )
        .expect_err("early exit must be distinguished from readiness timeout");
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(23));
                assert!(stderr.contains("startup-sentinel"), "{stderr}");
                assert!(
                    stderr.contains("stderr truncated after 16384 bytes"),
                    "retained stderr must be explicitly bounded: {stderr}"
                );
            }
            other => panic!("unexpected startup error: {other}"),
        }
    }

    #[test]
    fn a_child_that_lost_the_ownership_race_gives_the_live_owner_the_long_window() {
        // The spawned child exits naming a live owner; the owner answers only
        // after the short probe would have given up (2.7-7.9 s measured under
        // load on 2026-10-27). The probe is handed the long deadline, and the
        // launcher adopts the owner instead of refusing.
        let (child, stderr) = spawn_readiness_fixture(&format!(
            "printf 'trustd: fatal: cannot bind socket /s: {OWNED_ELSEWHERE} /s' >&2; exit 1"
        ));
        let started = Instant::now();
        let mut given = None;
        let ready = wait_with_held_lock(
            child,
            stderr,
            SPAWN_READY_TIMEOUT,
            LIVE_OWNER_ADOPT_TIMEOUT,
            |deadline| {
                // Before the child exits every probe is the short one (at most
                // OBSERVER_IO_TIMEOUT); only the post-exit probe gets the window.
                let window = deadline.saturating_duration_since(Instant::now());
                given = Some(window);
                (window > Duration::from_secs(10)).then_some("adopted").ok_or(ProbeMiss::NotServing)
            },
        )
        .expect("a live owner that answers inside the long window is adopted");
        assert_eq!(ready, "adopted");
        let window = given.expect("the post-exit probe ran");
        assert!(window > LIVE_OWNER_ADOPT_TIMEOUT - Duration::from_secs(10), "{window:?}");
        assert!(window <= LIVE_OWNER_ADOPT_TIMEOUT, "{window:?}");
        // The probe answered at once; the launcher never sleeps out the window.
        assert!(started.elapsed() < Duration::from_secs(30));
    }

    #[test]
    fn a_child_that_exited_for_another_reason_keeps_the_short_probe() {
        // An exit that names no live owner (a crash, a refused epoch) is not a
        // reason to wait: the last probe stays inside the observer bound, and
        // the refusal keeps its status and stderr. That holds even while the
        // endpoint is merely not serving: only a lost race re-probes.
        let (child, stderr) =
            spawn_readiness_fixture("printf 'trustd: fatal: epoch DIRTY' >&2; exit 1");
        let mut given = None;
        let started = Instant::now();
        let error = wait_with_held_lock(
            child,
            stderr,
            SPAWN_READY_TIMEOUT,
            LIVE_OWNER_ADOPT_TIMEOUT,
            |deadline| {
                given = Some(deadline.saturating_duration_since(Instant::now()));
                Err::<(), _>(ProbeMiss::NotServing)
            },
        )
        .expect_err("a child that exited for another reason is refused");
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains("epoch DIRTY"), "{stderr}");
            }
            other => panic!("unexpected startup error: {other}"),
        }
        assert!(given.expect("the post-exit probe ran") <= OBSERVER_IO_TIMEOUT);
        assert!(started.elapsed() < SPAWN_READY_TIMEOUT, "{:?}", started.elapsed());
    }

    #[test]
    fn the_ownership_refusal_carries_the_phrase_its_launcher_reads() {
        let dir =
            std::env::temp_dir().join(format!("trustd-owned-elsewhere-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("fixture dir");
        let path = dir.join("sentinel.lock");
        let first = File::create(&path).expect("first handle");
        let second = File::options().write(true).open(&path).expect("second handle");
        try_lock_stable_sentinel(&first, Path::new("/fixture/s.sock")).expect("first lock");
        let error = try_lock_stable_sentinel(&second, Path::new("/fixture/s.sock"))
            .expect_err("a held lock refuses a second owner");
        assert_eq!(error.kind(), std::io::ErrorKind::AddrInUse);
        assert!(error.to_string().contains(OWNED_ELSEWHERE), "{error}");
        drop((first, second));
        std::fs::remove_dir_all(dir).expect("remove fixture dir");
    }

    /// The identity a lost-race fixture's launcher expects; [`late_owner`]
    /// serves it, or a foreign one.
    fn lost_race_identity(digest: char) -> DaemonIdentity {
        DaemonIdentity {
            version: IDENTITY_VERSION.to_string(),
            protocol: STATUS_VERSION.to_string(),
            release: compiled_release().to_string(),
            commit: compiled_commit().to_string(),
            executable_sha256: digest.to_string().repeat(64),
        }
    }

    /// A child that loses the stable-ownership race the way `trustd` does
    /// ([`try_lock_stable_sentinel`]), and leaves `marker` just before it exits.
    fn spawn_lost_race_loser(marker: &Path) -> (std::process::Child, thread::JoinHandle<String>) {
        spawn_readiness_fixture(&format!(
            "printf 'trustd: fatal: cannot bind socket /s: {OWNED_ELSEWHERE} /s' >&2; : > '{}'; exit 1",
            marker.display()
        ))
    }

    /// The owner the loser lost to: it holds the stable lock (so the loser
    /// exited) but publishes only `delay` after the loser's `marker`, as a slow
    /// [`bind_owned_socket`] does: a stale socket there is reclaimed first, and
    /// the endpoint is renamed into place already private. It then serves
    /// `served` to every launcher that connects until `stop`, at most 30 s,
    /// and returns how many connected.
    fn late_owner(
        path: PathBuf,
        marker: PathBuf,
        delay: Duration,
        served: DaemonIdentity,
        stop: Arc<AtomicBool>,
    ) -> thread::JoinHandle<usize> {
        thread::spawn(move || {
            let until = Instant::now() + Duration::from_secs(30);
            while !marker.exists() && Instant::now() < until {
                thread::sleep(Duration::from_millis(5));
            }
            thread::sleep(delay);
            if socket_identity_at(&path).expect("stat the endpoint").is_some() {
                std::fs::remove_file(&path).expect("reclaim the stale socket");
            }
            let listener = bind_private_socket(&path).expect("publish the endpoint");
            listener.set_nonblocking(true).expect("nonblocking accept");
            let daemon = Daemon::with_budget_and_identity(4096, served);
            let mut connections = 0;
            while !stop.load(AtomicOrdering::SeqCst) && Instant::now() < until {
                match listener.accept() {
                    Ok((stream, _)) => {
                        connections += 1;
                        stream.set_nonblocking(false).expect("blocking connection");
                        // Returns at the launcher's EOF: it dropped its lease,
                        // or refused this daemon.
                        daemon.serve_conn(stream);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("accept a launcher: {error}"),
                }
            }
            connections
        })
    }

    /// Finding 2026-11-01 against 0c94bc4e6d: the owner a spawned child lost
    /// to holds the stable lock but has not published yet (bind_owned_socket
    /// locks first, then reclaims and binds). The launcher's one post-exit
    /// probe met a missing or stale endpoint, ended at once, and the run
    /// exited 3 although the owner was about to serve. Both shapes of "not
    /// yet" are waited out, and the owner is adopted.
    #[test]
    fn a_lost_race_adopts_an_owner_that_publishes_after_the_loser_exits() {
        for stale in [false, true] {
            let fixture = TestSocket::new("late-owner");
            let identity = lost_race_identity('d');
            if stale {
                // A dead predecessor's socket: connecting is ECONNREFUSED, once
                // no child another test forked still holds a copy of it.
                drop(bind_private_socket(&fixture.path).expect("bind the predecessor"));
                assert!(
                    listener_gone_within_hang_detector(&fixture.path),
                    "the predecessor's listener is gone"
                );
                assert_eq!(
                    lease_compatible_daemon_probe_until(
                        &fixture.path,
                        &identity,
                        Instant::now() + TEST_OBSERVER_TIMEOUT,
                        || 4096
                    )
                    .err(),
                    Some(ProbeMiss::NotServing),
                    "a stale endpoint is not serving"
                );
            }
            let marker = fixture.path.with_file_name("loser-exited");
            let stop = Arc::new(AtomicBool::new(false));
            let owner = late_owner(
                fixture.path.clone(),
                marker.clone(),
                Duration::from_secs(1),
                identity.clone(),
                Arc::clone(&stop),
            );
            let (child, stderr) = spawn_lost_race_loser(&marker);
            let started = Instant::now();
            let result = wait_with_held_lock(
                child,
                stderr,
                SPAWN_READY_TIMEOUT,
                LIVE_OWNER_ADOPT_TIMEOUT,
                |deadline| {
                    lease_compatible_daemon_probe_until(&fixture.path, &identity, deadline, || 4096)
                },
            );
            let waited = started.elapsed();
            let adopted = result.is_ok();
            drop(result);
            stop.store(true, AtomicOrdering::SeqCst);
            // One connection, or two when a probe met the socket renamed into
            // place mid-connect (`ProbeMiss::of_connect`) and tried again.
            let connections = owner.join().expect("late owner joined");
            let _ = std::fs::remove_file(&marker);
            assert!(adopted, "stale={stale}: the owner that published late is adopted");
            assert!(connections >= 1, "stale={stale}: the late owner served the lease");
            assert!(waited >= Duration::from_secs(1), "stale={stale}: {waited:?}");
            assert!(waited < LIVE_OWNER_ADOPT_TIMEOUT, "stale={stale}: {waited:?}");
        }
    }

    /// A definite answer is never retried into adoption: an endpoint that
    /// appears during the window with a foreign identity (another toolchain's
    /// daemon) ends the wait at its first answer, refused.
    #[test]
    fn a_lost_race_refuses_a_foreign_identity_that_appears_in_the_window() {
        let fixture = TestSocket::new("late-foreign");
        let marker = fixture.path.with_file_name("loser-exited");
        let stop = Arc::new(AtomicBool::new(false));
        let owner = late_owner(
            fixture.path.clone(),
            marker.clone(),
            Duration::from_millis(500),
            lost_race_identity('e'),
            Arc::clone(&stop),
        );
        let (child, stderr) = spawn_lost_race_loser(&marker);
        let expected = lost_race_identity('d');
        let started = Instant::now();
        let error = wait_with_held_lock(
            child,
            stderr,
            SPAWN_READY_TIMEOUT,
            LIVE_OWNER_ADOPT_TIMEOUT,
            |deadline| {
                lease_compatible_daemon_probe_until(&fixture.path, &expected, deadline, || 4096)
            },
        )
        .expect_err("a foreign identity is never adopted");
        let waited = started.elapsed();
        // Give a retrying launcher time to connect again before counting.
        thread::sleep(Duration::from_millis(300));
        stop.store(true, AtomicOrdering::SeqCst);
        let connections = owner.join().expect("foreign owner joined");
        let _ = std::fs::remove_file(&marker);
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains(OWNED_ELSEWHERE), "{stderr}");
            }
            other => panic!("unexpected startup error: {other}"),
        }
        assert_eq!(connections, 1, "refused at its first answer, never asked again");
        assert!(waited >= Duration::from_millis(500), "{waited:?}");
        assert!(waited < Duration::from_secs(30), "ended at the first answer: {waited:?}");
    }

    /// An owner that holds the lock and never serves is refused at the
    /// deadline: the re-probing is bounded, and it did re-probe. Every try of
    /// the post-exit wait shares the wait's one deadline ([`ProbeLog`]); each
    /// probe before the exit gets its own.
    #[test]
    fn a_lost_race_to_an_owner_that_never_publishes_is_refused_at_its_deadline() {
        let fixture = TestSocket::new("never-owner");
        let marker = fixture.path.with_file_name("loser-exited");
        let (child, stderr) = spawn_lost_race_loser(&marker);
        let identity = lost_race_identity('d');
        let (timeout, window) = (Duration::from_millis(1500), Duration::from_secs(2));
        let mut log = ProbeLog::default();
        let error = wait_with_held_lock(child, stderr, timeout, window, |deadline| {
            log.record(deadline);
            lease_compatible_daemon_probe_until(&fixture.path, &identity, deadline, || 4096)
        })
        .expect_err("an owner that never serves is refused");
        let ended = Instant::now();
        let _ = std::fs::remove_file(&marker);
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains(OWNED_ELSEWHERE), "{stderr}");
            }
            other => panic!("unexpected startup error: {other}"),
        }
        log.assert_one_window(timeout, window, ended, Duration::from_secs(2));
    }

    /// The owner a child lost to released the lock without serving (it exited
    /// in startup): the launcher stops waiting and spawns once more. That
    /// child's own refusal is reported; and a second vanished owner is refused
    /// without a third spawn.
    #[test]
    fn a_vanished_owner_costs_one_more_spawn_and_no_more() {
        for (second, expected) in [
            ("printf 'trustd: fatal: epoch DIRTY' >&2; exit 1".to_string(), "epoch DIRTY"),
            (
                format!(
                    "printf 'trustd: fatal: cannot bind socket /s: {OWNED_ELSEWHERE} /s' >&2; exit 1"
                ),
                OWNED_ELSEWHERE,
            ),
        ] {
            let mut spawned = 0usize;
            let mut released_asked = 0usize;
            let started = Instant::now();
            let error = spawn_until_adopted(
                Path::new("/fixture/trustd"),
                SPAWN_READY_TIMEOUT,
                LIVE_OWNER_ADOPT_TIMEOUT,
                || {
                    spawned += 1;
                    Ok(if spawned == 1 {
                        spawn_readiness_fixture(&format!(
                            "printf 'trustd: fatal: cannot bind socket /s: {OWNED_ELSEWHERE} /s' >&2; exit 1"
                        ))
                    } else {
                        spawn_readiness_fixture(&second)
                    })
                },
                &mut || {
                    released_asked += 1;
                    true
                },
                |_| Err::<(), _>(ProbeMiss::NotServing),
            )
            .expect_err("nothing ever serves");
            match error {
                EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                    assert_eq!(status.code(), Some(1));
                    assert!(stderr.contains(expected), "{expected}: {stderr}");
                }
                other => panic!("unexpected startup error: {other}"),
            }
            assert_eq!(spawned, 2, "{expected}: exactly one more spawn");
            assert!(released_asked >= 1, "{expected}");
            assert!(started.elapsed() < Duration::from_secs(30), "{expected}: no window waited");
        }
    }

    /// True once `holds` does, polled every 10 ms.
    ///
    /// For a condition that a descriptor closing in THIS process makes true,
    /// such as a stable lock released by dropping its owner: a child another
    /// test forks meanwhile holds a copy of every descriptor until it execs
    /// (see [`listener_gone_within_hang_detector`]), and with that copy the
    /// lock. The deadline is a hang detector, not a latency budget: a condition
    /// that never comes true still fails.
    fn holds_within_hang_detector(mut holds: impl FnMut() -> bool) -> bool {
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if holds() {
                return true;
            }
            if Instant::now() >= deadline {
                return false;
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    /// Removes fixture files when a test ends, panicking or not, so the
    /// directory [`TestSocket`] removes after it is empty.
    struct RemoveOnDrop(Vec<PathBuf>);

    impl Drop for RemoveOnDrop {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = std::fs::remove_file(path);
            }
        }
    }

    /// The release check reads the lock and nothing else: `true` only for a
    /// valid sentinel nobody holds, and it leaves the lock free for the next
    /// owner.
    #[test]
    fn the_owner_is_released_only_when_its_stable_lock_is_free() {
        use std::os::unix::fs::symlink;

        let fixture = TestSocket::new("owner-released");
        let dir = fixture.path.parent().expect("fixture parent").to_path_buf();
        let sentinel = dir.join("sentinel.lock");
        let alias = dir.join("alias.lock");
        let _cleanup = RemoveOnDrop(vec![alias.clone(), sentinel.clone()]);
        assert!(!stable_owner_released(&sentinel), "no sentinel is not a released one");

        let owner = stable_sentinel_options().create_new(true).open(&sentinel).expect("sentinel");
        try_lock_stable_sentinel(&owner, Path::new("/fixture/s.sock")).expect("owner locks");
        assert!(!stable_owner_released(&sentinel), "a live owner holds it");
        drop(owner);
        assert!(
            holds_within_hang_detector(|| stable_owner_released(&sentinel)),
            "the owner exited"
        );
        let next = stable_sentinel_options().open(&sentinel).expect("reopen");
        // A child forked while the check held its shared lock keeps it until
        // it execs; a check that kept the lock itself never lets go.
        assert!(
            holds_within_hang_detector(|| {
                try_lock_stable_sentinel(&next, Path::new("/fixture/s.sock")).is_ok()
            }),
            "the check left the lock free for the next owner"
        );
        drop(next);

        symlink(&sentinel, &alias).expect("alias the sentinel");
        assert!(!stable_owner_released(&alias), "a symlink is never the sentinel");
        std::fs::set_permissions(&sentinel, std::fs::Permissions::from_mode(0o644))
            .expect("open the sentinel to others");
        assert!(!stable_owner_released(&sentinel), "an invalid sentinel is not a released one");
        for path in [&alias, &sentinel] {
            std::fs::remove_file(path).expect("remove fixture file");
        }
    }

    /// Finding 2026-11-01 (review of the lost-race wait): no test reached the
    /// release check `ensure_daemon` wires into the wait, only the helper it
    /// calls. Wired to answer "released" whenever it can name a sentinel, it
    /// brought the original bug back: the launcher spawned again, the second
    /// child lost to the same unpublished owner, and the run exited 3 within
    /// milliseconds. The check asks the very lock `trustd` takes for that
    /// socket: "held" before any owner and while one lives, "released" once it
    /// is gone.
    #[test]
    fn the_wired_release_check_reads_the_lock_trustd_takes_for_that_socket() {
        let fixture = TestSocket::new("wired-release");
        let mut released = stable_owner_released_for_socket(&fixture.path);
        // The sentinel is located on this first call, before it exists.
        assert!(!released(), "no sentinel yet is not a released one");
        let owned = bind_owned_socket(&fixture.path).expect("an owner takes the stable lock");
        assert!(!released(), "the owner holds the lock it took for this socket");
        assert!(!released(), "and still holds it on the next try");
        owned.mark_clean().expect("fixture proves a quiescent clean shutdown");
        drop(owned);
        assert!(holds_within_hang_detector(&mut released), "the owner exited");
    }

    /// Whether the launcher has reaped the child `pid` (0: not spawned yet).
    /// Until then the child is a zombie that `kill(pid, 0)` still reaches;
    /// [`wait_for_spawned_daemon`] reaps it and goes straight on to its
    /// post-exit wait.
    fn reaped(pid: u32) -> bool {
        pid != 0
            && unsafe { libc::kill(pid as libc::pid_t, 0) } == -1
            && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH)
    }

    /// An owner that holds the stable lock `lock` (taken by the caller before
    /// any launcher can look), publishes its endpoint once the launcher has
    /// reaped the `loser` (so only its post-exit wait can meet the endpoint,
    /// not the probes it makes while the child runs), and then dies before it
    /// answers: it closes the first launcher's connection unanswered, as a
    /// `trustd` whose startup failed after its bind does, or one that exited
    /// idle while the launcher sat in its listen queue. With
    /// `release_after: Some(lag)` it then closes its listener and, `lag` later
    /// (an owner syncing its CLEAN epoch), its lock, as that exit would. With
    /// `None` it lives on, holding both and counting every launcher that
    /// connects, until `stop` (at most 30 s). Returns how many connected.
    fn owner_that_dies_unanswered(
        path: PathBuf,
        loser: Arc<AtomicU32>,
        lock: File,
        release_after: Option<Duration>,
        stop: Arc<AtomicBool>,
    ) -> thread::JoinHandle<usize> {
        thread::spawn(move || {
            let until = Instant::now() + Duration::from_secs(30);
            while !reaped(loser.load(AtomicOrdering::SeqCst)) && Instant::now() < until {
                thread::sleep(Duration::from_millis(5));
            }
            let listener = bind_private_socket(&path).expect("publish the endpoint");
            listener.set_nonblocking(true).expect("nonblocking accept");
            let mut connections = 0;
            loop {
                let done = match release_after {
                    None => stop.load(AtomicOrdering::SeqCst),
                    Some(_) => connections > 0,
                };
                if done || Instant::now() >= until {
                    break;
                }
                match listener.accept() {
                    // Closed unanswered: the launcher reads end of stream.
                    Ok((stream, _)) => {
                        connections += 1;
                        drop(stream);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("accept a launcher: {error}"),
                }
            }
            drop(listener);
            thread::sleep(release_after.unwrap_or_default());
            drop(lock);
            connections
        })
    }

    /// Finding 2026-11-01 (review of the lost-race wait): the owner a child
    /// lost to published and then died before it answered. The launcher's
    /// probe met the closed exchange, a definite refusal, and the run exited 3
    /// although nothing held the stable lock any more, where `ensure_daemon`
    /// treats a daemon that refuses as it closes as absent. A refusal is still
    /// never retried into adoption: the launcher asks whether the lock is free
    /// and, only when it is, spawns once more, also when the lock comes free
    /// a little after the refusal. An owner that refuses and lives is refused
    /// as before, asked once.
    #[test]
    fn a_lost_race_to_an_owner_that_dies_unanswered_spawns_again() {
        for release_after in [Some(Duration::ZERO), Some(Duration::from_millis(300)), None] {
            let keep_lock = release_after.is_none();
            let fixture = TestSocket::new("dying-owner");
            let sentinel = fixture.path.with_file_name("sentinel.lock");
            let marker = fixture.path.with_file_name("loser-exited");
            let _cleanup = RemoveOnDrop(vec![sentinel.clone(), marker.clone()]);
            let lock =
                stable_sentinel_options().create_new(true).open(&sentinel).expect("sentinel");
            try_lock_stable_sentinel(&lock, Path::new("/fixture/s.sock")).expect("owner locks");
            let stop = Arc::new(AtomicBool::new(false));
            let loser = Arc::new(AtomicU32::new(0));
            let owner = owner_that_dies_unanswered(
                fixture.path.clone(),
                Arc::clone(&loser),
                lock,
                release_after,
                Arc::clone(&stop),
            );
            let identity = lost_race_identity('d');
            let mut spawned = 0usize;
            let started = Instant::now();
            let error = spawn_until_adopted(
                Path::new("/fixture/trustd"),
                SPAWN_READY_TIMEOUT,
                LIVE_OWNER_ADOPT_TIMEOUT,
                || {
                    spawned += 1;
                    Ok(if spawned == 1 {
                        let (child, stderr) = spawn_lost_race_loser(&marker);
                        loser.store(child.id(), AtomicOrdering::SeqCst);
                        (child, stderr)
                    } else {
                        spawn_readiness_fixture("printf 'trustd: fatal: epoch DIRTY' >&2; exit 1")
                    })
                },
                &mut || stable_owner_released(&sentinel),
                |deadline| {
                    lease_compatible_daemon_probe_until(&fixture.path, &identity, deadline, || 4096)
                },
            )
            .expect_err("nothing ever serves a lease");
            let waited = started.elapsed();
            stop.store(true, AtomicOrdering::SeqCst);
            let connections = owner.join().expect("owner joined");
            let stderr = match error {
                EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                    assert_eq!(status.code(), Some(1), "release_after={release_after:?}");
                    stderr
                }
                other => {
                    panic!("release_after={release_after:?}: unexpected startup error: {other}")
                }
            };
            assert_eq!(connections, 1, "release_after={release_after:?}: asked once, never again");
            if keep_lock {
                assert_eq!(spawned, 1, "an owner that refuses and lives is not spawned past");
                assert!(stderr.contains(OWNED_ELSEWHERE), "{stderr}");
            } else {
                assert_eq!(spawned, 2, "the dead owner's lock is free: one more spawn");
                assert!(stderr.contains("epoch DIRTY"), "the second child's refusal: {stderr}");
            }
            assert!(
                waited < Duration::from_secs(30),
                "release_after={release_after:?}: {waited:?}"
            );
        }
    }

    /// Finding 2026-11-01 (review of the lost-race wait): the release check
    /// opened the sentinel read-only without `O_NONBLOCK`, and such an open
    /// of a FIFO waits for a writer, with no deadline: a FIFO at the sentinel
    /// path hung the launcher. A FIFO is not a sentinel, so the answer is
    /// "held", at once.
    #[test]
    fn the_release_check_never_waits_on_a_fifo_at_the_sentinel_path() {
        use std::os::unix::ffi::OsStrExt as _;

        let fixture = TestSocket::new("owner-fifo");
        let fifo = fixture.path.with_file_name("sentinel.lock");
        let _cleanup = RemoveOnDrop(vec![fifo.clone()]);
        let c_path = std::ffi::CString::new(fifo.as_os_str().as_bytes()).expect("no NUL in path");
        assert_eq!(
            unsafe { libc::mkfifo(c_path.as_ptr(), 0o600) },
            0,
            "mkfifo: {}",
            std::io::Error::last_os_error()
        );
        let (sender, answers) = std::sync::mpsc::channel();
        let checked = fifo.clone();
        let checker = thread::spawn(move || {
            let _ = sender.send(stable_owner_released(&checked));
        });
        // A hang detector, not a latency budget.
        let answer = answers.recv_timeout(Duration::from_secs(60));
        if answer.is_err() {
            // Open the other end so the stuck check can return, then fail.
            let writer = OpenOptions::new().read(true).write(true).open(&fifo);
            let _ = checker.join();
            drop(writer);
            panic!("the release check blocked opening a FIFO at the sentinel path");
        }
        checker.join().expect("checker joined");
        assert_eq!(answer, Ok(false), "a FIFO is not a sentinel, so it is not a released one");
    }

    /// What one probe of the lost-race wait learns, endpoint by endpoint:
    /// only a missing or stale endpoint is "not serving yet".
    #[test]
    fn only_a_missing_or_stale_endpoint_is_not_serving() {
        let expected = lost_race_identity('d');
        let probe = |path: &Path| {
            lease_compatible_daemon_probe_until(
                path,
                &expected,
                Instant::now() + TEST_OBSERVER_TIMEOUT,
                || 4096,
            )
            .err()
        };
        let fixture = TestSocket::new("probe-miss");
        assert_eq!(probe(&fixture.path), Some(ProbeMiss::NotServing), "missing");
        drop(bind_private_socket(&fixture.path).expect("bind then close"));
        // Stale once no child another test forked still holds a copy of it.
        assert!(listener_gone_within_hang_detector(&fixture.path), "the listener is gone");
        assert_eq!(probe(&fixture.path), Some(ProbeMiss::NotServing), "stale");
        std::fs::set_permissions(&fixture.path, std::fs::Permissions::from_mode(0o666))
            .expect("open the stale socket to others");
        assert_eq!(probe(&fixture.path), Some(ProbeMiss::Refused), "non-private");
        std::fs::remove_file(&fixture.path).expect("remove the stale socket");
        File::create(&fixture.path).expect("a regular file at the path");
        assert_eq!(probe(&fixture.path), Some(ProbeMiss::Refused), "not a socket");
        std::fs::remove_file(&fixture.path).expect("remove the regular file");

        for (label, served, closing) in [
            ("foreign identity", lost_race_identity('e'), false),
            ("refused lease", expected.clone(), true),
        ] {
            let listener = bind_private_socket(&fixture.path).expect("bind responder");
            let daemon = Daemon::with_budget_and_identity(4096, served);
            if closing {
                outlast_the_idle_bound(&daemon);
                assert!(daemon.try_begin_idle_shutdown(), "admission closed");
            }
            let server = spawn_ready_responder(move || {
                let (stream, _) = listener.accept().expect("accept the probe");
                daemon.serve_conn(stream);
            });
            assert_eq!(probe(&fixture.path), Some(ProbeMiss::Refused), "{label}");
            server.join().expect("responder joined");
            std::fs::remove_file(&fixture.path).expect("remove the responder's socket");
        }
    }

    /// The owner the loser lost to, at its connection limit: it publishes as
    /// [`late_owner`] does, 300 ms after the loser's `marker` (so the
    /// launcher's post-exit wait, not a probe it makes while the child runs,
    /// meets it), with every connection slot taken. Its first `busy_answers`
    /// launchers get the real rejection ([`Daemon::admit_connection`] answers
    /// [`BUSY_REPLY`]); a later one finds the slots freed and is served
    /// `served`. With `release: Some((after, lock))` it closes its listener
    /// `after` it published and then drops its stable `lock`, as an owner that
    /// exits does; otherwise it lives until `stop`, at most 30 s. Returns how
    /// many launchers connected.
    fn saturated_owner(
        path: PathBuf,
        marker: PathBuf,
        busy_answers: usize,
        served: DaemonIdentity,
        release: Option<(Duration, File)>,
        stop: Arc<AtomicBool>,
    ) -> thread::JoinHandle<usize> {
        thread::spawn(move || {
            let until = Instant::now() + Duration::from_secs(30);
            while !marker.exists() && Instant::now() < until {
                thread::sleep(Duration::from_millis(5));
            }
            thread::sleep(Duration::from_millis(300));
            let listener = bind_private_socket(&path).expect("publish the endpoint");
            listener.set_nonblocking(true).expect("nonblocking accept");
            let published = Instant::now();
            let daemon = Daemon::with_budget_and_identity(4096, served);
            let mut slots: Vec<_> = (0..MAX_SERVER_CONNECTIONS)
                .map(|_| daemon.try_acquire_connection().expect("fill a connection slot"))
                .collect();
            let (release_after, lock) = match release {
                Some((after, lock)) => (Some(after), Some(lock)),
                None => (None, None),
            };
            let mut connections = 0usize;
            loop {
                let exiting = release_after.is_some_and(|after| published.elapsed() >= after);
                if exiting || stop.load(AtomicOrdering::SeqCst) || Instant::now() >= until {
                    break;
                }
                match listener.accept() {
                    Ok((stream, _)) => {
                        connections += 1;
                        stream.set_nonblocking(false).expect("blocking connection");
                        if connections > busy_answers {
                            slots.clear();
                        }
                        // At the limit this is the real `ERR busy`, an error by
                        // design. A served connection returns at the
                        // launcher's EOF: it dropped its lease.
                        if let Ok((permit, stream)) = daemon.admit_connection(stream) {
                            permit.serve(stream);
                        }
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("accept a launcher: {error}"),
                }
            }
            drop(listener);
            drop(lock);
            connections
        })
    }

    /// The requests a lost-race probe sends, in order
    /// ([`lease_compatible_daemon_probe_until`]).
    const PROBE_REQUESTS: [&str; 3] = ["IDENTITY", "STATUS", "LEASE"];

    /// Send `reply` on an accepted probe the way a saturated `trustd` sends
    /// its rejection: at once, before reading the request; then drain until
    /// the prober closes (a hang detector bounds the drain). With `answered`
    /// lines, answer the first [`PROBE_REQUESTS`] with them in turn and send
    /// `reply` in answer to the next request instead (STATUS after one line,
    /// LEASE after two).
    fn answer_raw(mut stream: UnixStream, reply: &[u8], answered: &[String]) {
        // A prober that already left (one whose deadline had passed connects and
        // closes at once) makes macOS fail this with `EINVAL`
        // ([`busy_peer_has_left`]); the drain below then ends at once anyway.
        let _ = stream.set_read_timeout(Some(Duration::from_secs(30)));
        if !answered.is_empty() {
            let mut reader = BufReader::new(stream.try_clone().expect("clone the probe"));
            let mut request = String::new();
            for (expected, answer) in PROBE_REQUESTS.iter().zip(answered) {
                request.clear();
                reader.read_line(&mut request).expect("read a request");
                assert_eq!(request, format!("{expected}\n"));
                stream.write_all(format!("{answer}\n").as_bytes()).expect("answer it");
            }
            request.clear();
            reader.read_line(&mut request).expect("read the request `reply` answers");
            assert_eq!(request, format!("{}\n", PROBE_REQUESTS[answered.len()]));
        }
        let _ = stream.write_all(reply);
        let _ = stream.shutdown(std::net::Shutdown::Write);
        let mut sink = Vec::new();
        let _ = stream.read_to_end(&mut sink);
    }

    /// An owner like [`saturated_owner`] (never released) whose every answer
    /// is `reply`, sent by [`answer_raw`]. Counts launchers until `stop`, at
    /// most 30 s.
    fn raw_owner(
        path: PathBuf,
        marker: PathBuf,
        reply: &'static [u8],
        stop: Arc<AtomicBool>,
    ) -> thread::JoinHandle<usize> {
        thread::spawn(move || {
            let until = Instant::now() + Duration::from_secs(30);
            while !marker.exists() && Instant::now() < until {
                thread::sleep(Duration::from_millis(5));
            }
            thread::sleep(Duration::from_millis(300));
            let listener = bind_private_socket(&path).expect("publish the endpoint");
            listener.set_nonblocking(true).expect("nonblocking accept");
            let mut connections = 0usize;
            while !stop.load(AtomicOrdering::SeqCst) && Instant::now() < until {
                match listener.accept() {
                    Ok((stream, _)) => {
                        connections += 1;
                        stream.set_nonblocking(false).expect("blocking connection");
                        answer_raw(stream, reply, &[]);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("accept a launcher: {error}"),
                }
            }
            connections
        })
    }

    /// TRUSTD-LOST-RACE-2: the owner a spawned child lost to is alive but at
    /// its connection limit, and answers `ERR busy`. That says nothing about
    /// who it is, so the launcher asks again inside the same window, and
    /// adopts the owner once a slot is free and it serves the exact identity.
    /// Before, the first `ERR busy` was a refusal and the run exited 3.
    #[test]
    fn a_lost_race_waits_out_a_busy_owner_and_adopts_it_once_it_serves() {
        const BUSY_ANSWERS: usize = 5;
        let fixture = TestSocket::new("busy-owner");
        let marker = fixture.path.with_file_name("loser-exited");
        let _cleanup = RemoveOnDrop(vec![marker.clone()]);
        let identity = lost_race_identity('d');
        let stop = Arc::new(AtomicBool::new(false));
        let owner = saturated_owner(
            fixture.path.clone(),
            marker.clone(),
            BUSY_ANSWERS,
            identity.clone(),
            None,
            Arc::clone(&stop),
        );
        let (child, stderr) = spawn_lost_race_loser(&marker);
        let mut busy_seen = 0usize;
        let started = Instant::now();
        let result = wait_with_held_lock(
            child,
            stderr,
            SPAWN_READY_TIMEOUT,
            LIVE_OWNER_ADOPT_TIMEOUT,
            |deadline| {
                let probe =
                    lease_compatible_daemon_probe_until(&fixture.path, &identity, deadline, || {
                        4096
                    });
                busy_seen += usize::from(probe.as_ref().err() == Some(&ProbeMiss::Busy));
                probe
            },
        );
        let waited = started.elapsed();
        let adopted = result.is_ok();
        drop(result);
        stop.store(true, AtomicOrdering::SeqCst);
        let connections = owner.join().expect("busy owner joined");
        assert!(adopted, "the owner that answered ERR busy and then served is adopted");
        assert!(busy_seen >= 1, "the owner was met busy ({busy_seen} busy answers)");
        assert!(connections > busy_seen, "asked again after ERR busy: {connections} connections");
        assert!(waited < LIVE_OWNER_ADOPT_TIMEOUT, "{waited:?}");
    }

    /// TRUSTD-LOST-RACE-2: an owner busy for the whole window is refused AT
    /// the window's deadline, with the child's early exit: not at its first
    /// `ERR busy` (which a refusal would be, after the release grace), and
    /// not later (no grace or second window follows a busy deadline). Every
    /// post-exit try shares the one deadline, set at the exit and never moved
    /// by a busy answer, and the tries are spaced by the poll interval
    /// ([`ProbeLog::assert_one_window`]). Then the same against a real
    /// saturated owner over its socket.
    #[test]
    fn a_lost_race_to_an_owner_busy_for_the_whole_window_is_refused_at_its_deadline() {
        let (timeout, window) = (Duration::from_millis(1500), Duration::from_secs(3));
        assert!(window > REFUSING_OWNER_RELEASE_GRACE + Duration::from_millis(500));
        let (child, stderr) = spawn_readiness_fixture(&format!(
            "printf 'trustd: fatal: cannot bind socket /s: {OWNED_ELSEWHERE} /s' >&2; exit 1"
        ));
        let mut log = ProbeLog::default();
        let error = wait_with_held_lock(child, stderr, timeout, window, |deadline| {
            log.record(deadline);
            Err::<(), _>(ProbeMiss::Busy)
        })
        .expect_err("an owner busy for the whole window is refused");
        let ended = Instant::now();
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains(OWNED_ELSEWHERE), "{stderr}");
            }
            other => panic!("unexpected startup error: {other}"),
        }
        log.assert_one_window(timeout, window, ended, Duration::from_secs(1));

        // End to end: the real rejection, from an owner whose slots never free.
        let fixture = TestSocket::new("busy-window");
        let marker = fixture.path.with_file_name("loser-exited");
        let _cleanup = RemoveOnDrop(vec![marker.clone()]);
        let identity = lost_race_identity('d');
        let stop = Arc::new(AtomicBool::new(false));
        let owner = saturated_owner(
            fixture.path.clone(),
            marker.clone(),
            usize::MAX,
            identity.clone(),
            None,
            Arc::clone(&stop),
        );
        let (child, stderr) = spawn_lost_race_loser(&marker);
        let window = Duration::from_secs(4);
        let mut log = ProbeLog::default();
        let mut busy_seen = 0usize;
        let error = wait_with_held_lock(child, stderr, timeout, window, |deadline| {
            log.record(deadline);
            let probe =
                lease_compatible_daemon_probe_until(&fixture.path, &identity, deadline, || 4096);
            busy_seen += usize::from(probe.as_ref().err() == Some(&ProbeMiss::Busy));
            probe
        })
        .expect_err("a saturated owner is never adopted");
        let ended = Instant::now();
        stop.store(true, AtomicOrdering::SeqCst);
        let connections = owner.join().expect("saturated owner joined");
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains(OWNED_ELSEWHERE), "{stderr}");
            }
            other => panic!("unexpected startup error: {other}"),
        }
        assert!(busy_seen > 2, "the owner was met busy again and again: {busy_seen} busy answers");
        assert!(connections >= busy_seen, "{connections} connections, {busy_seen} busy answers");
        log.assert_one_window(timeout, window, ended, Duration::from_secs(2));
    }

    /// TRUSTD-LOST-RACE-2: an owner that releases its stable lock while it is
    /// answering `ERR busy` has exited, so nothing will serve: the wait ends
    /// as [`SpawnedDaemon::OwnerVanished`] (not as a refusal), and the
    /// launcher spawns once more. The release comes after the refusal grace
    /// would have ended, so a launcher that took `ERR busy` for a refusal
    /// exits 3 instead.
    #[test]
    fn a_lost_race_to_a_busy_owner_that_exits_spawns_again() {
        let release_after = REFUSING_OWNER_RELEASE_GRACE + Duration::from_secs(1);
        let (child, stderr) = spawn_readiness_fixture(&format!(
            "printf 'trustd: fatal: cannot bind socket /s: {OWNED_ELSEWHERE} /s' >&2; exit 1"
        ));
        let release_at = Instant::now() + release_after;
        let mut released = || Instant::now() >= release_at;
        let mut busy = 0usize;
        let outcome = wait_for_spawned_daemon(
            child,
            stderr,
            Path::new("/fixture/trustd"),
            Duration::from_millis(1500),
            LostRaceWait { window: LIVE_OWNER_ADOPT_TIMEOUT, owner_released: &mut released },
            |_| {
                busy += 1;
                Err::<(), _>(ProbeMiss::Busy)
            },
        );
        match outcome {
            Ok(SpawnedDaemon::OwnerVanished { status, stderr }) => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains(OWNED_ELSEWHERE), "{stderr}");
            }
            other => panic!("a busy owner that exits has vanished: {other:?}"),
        }
        assert!(Instant::now() >= release_at, "ended by the release, not before it");
        assert!(busy > 2, "asked again while busy: {busy} tries");

        // End to end: the real rejection and the real stable lock.
        let fixture = TestSocket::new("busy-exits");
        let sentinel = fixture.path.with_file_name("sentinel.lock");
        let marker = fixture.path.with_file_name("loser-exited");
        let _cleanup = RemoveOnDrop(vec![sentinel.clone(), marker.clone()]);
        let lock = stable_sentinel_options().create_new(true).open(&sentinel).expect("sentinel");
        try_lock_stable_sentinel(&lock, Path::new("/fixture/s.sock")).expect("owner locks");
        let identity = lost_race_identity('d');
        let stop = Arc::new(AtomicBool::new(false));
        let owner = saturated_owner(
            fixture.path.clone(),
            marker.clone(),
            usize::MAX,
            identity.clone(),
            Some((release_after, lock)),
            Arc::clone(&stop),
        );
        let (mut spawned, mut busy_seen) = (0usize, 0usize);
        let started = Instant::now();
        let error = spawn_until_adopted(
            Path::new("/fixture/trustd"),
            SPAWN_READY_TIMEOUT,
            LIVE_OWNER_ADOPT_TIMEOUT,
            || {
                spawned += 1;
                Ok(if spawned == 1 {
                    spawn_lost_race_loser(&marker)
                } else {
                    spawn_readiness_fixture("printf 'trustd: fatal: epoch DIRTY' >&2; exit 1")
                })
            },
            &mut || stable_owner_released(&sentinel),
            |deadline| {
                let probe =
                    lease_compatible_daemon_probe_until(&fixture.path, &identity, deadline, || {
                        4096
                    });
                busy_seen += usize::from(probe.as_ref().err() == Some(&ProbeMiss::Busy));
                probe
            },
        )
        .expect_err("nothing ever serves a lease");
        let waited = started.elapsed();
        stop.store(true, AtomicOrdering::SeqCst);
        let connections = owner.join().expect("saturated owner joined");
        match error {
            EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                assert_eq!(status.code(), Some(1));
                assert!(stderr.contains("epoch DIRTY"), "the second child's refusal: {stderr}");
            }
            other => panic!("unexpected startup error: {other}"),
        }
        assert_eq!(spawned, 2, "the busy owner's lock came free: one more spawn");
        assert!(busy_seen > 1, "asked again while busy: {busy_seen} busy answers");
        assert!(connections >= busy_seen, "{connections} connections");
        assert!(waited >= release_after, "{waited:?}");
        assert!(waited < Duration::from_secs(30), "{waited:?}");
    }

    /// TRUSTD-LOST-RACE-2: only the exact framed line `ERR busy`, as the
    /// answer to IDENTITY, is a busy answer. The real saturated daemon's
    /// rejection is one (the positive control that ties the server's frame to
    /// the client's match); a line that differs by any byte, lacks its
    /// newline, or is some other error or garbage stays a refusal, and so
    /// does `ERR busy` in answer to STATUS or LEASE, where no saturated daemon
    /// sends it. Positive control for those two: the same exchange answering
    /// LEASE with `LEASED` is adopted, so the identity and STATUS lines the
    /// responder sends are accepted and the refusal is the busy line's. What
    /// follows a busy line is never read (a busy answer is never adopted, so
    /// nothing after it can matter).
    #[test]
    fn only_the_exact_busy_line_is_a_busy_answer() {
        let expected = lost_race_identity('d');
        let probe = |path: &Path| {
            lease_compatible_daemon_probe_until(
                path,
                &expected,
                Instant::now() + TEST_OBSERVER_TIMEOUT,
                || 4096,
            )
            .err()
        };
        let fixture = TestSocket::new("busy-line");

        let listener = bind_private_socket(&fixture.path).expect("bind saturated responder");
        let daemon = Daemon::with_budget_and_identity(4096, expected.clone());
        let slots: Vec<_> = (0..MAX_SERVER_CONNECTIONS)
            .map(|_| daemon.try_acquire_connection().expect("fill a connection slot"))
            .collect();
        let server = spawn_ready_responder(move || {
            let (stream, _) = listener.accept().expect("accept the probe");
            let error = daemon.admit_connection(stream).err().expect("over the limit");
            assert_eq!(error.kind(), std::io::ErrorKind::WouldBlock, "{error}");
            drop(slots);
        });
        assert_eq!(probe(&fixture.path), Some(ProbeMiss::Busy), "the real rejection");
        server.join().expect("saturated responder joined");
        std::fs::remove_file(&fixture.path).expect("remove the responder's socket");

        // What a served daemon answers IDENTITY and STATUS with, in turn.
        let served = [
            serde_json::to_string(&expected).expect("identity JSON"),
            Daemon::with_budget_and_identity(4096, expected.clone()).handle_line("STATUS"),
        ];
        // (reply, how many of `served` answer the requests before it, verdict)
        let cases: [(&'static [u8], usize, Option<ProbeMiss>); 14] = [
            (b"ERR busy\n", 0, Some(ProbeMiss::Busy)),
            (b"ERR busy\nanything\n", 0, Some(ProbeMiss::Busy)),
            (b"ERR busyX\n", 0, Some(ProbeMiss::Refused)),
            (b"ERR busy \n", 0, Some(ProbeMiss::Refused)),
            (b" ERR busy\n", 0, Some(ProbeMiss::Refused)),
            (b"ERR busy\r\n", 0, Some(ProbeMiss::Refused)),
            (b"err busy\n", 0, Some(ProbeMiss::Refused)),
            (b"ERR other\n", 0, Some(ProbeMiss::Refused)),
            (b"garbage\n", 0, Some(ProbeMiss::Refused)),
            (b"ERR busy", 0, Some(ProbeMiss::Refused)),
            (b"ERR busy\n", 1, Some(ProbeMiss::Refused)),
            (b"ERR busy\n", 2, Some(ProbeMiss::Refused)),
            (b"LEASED\n", 2, None),
            (b"garbage\n", 2, Some(ProbeMiss::Refused)),
        ];
        for (reply, answered, want) in cases {
            let label = format!(
                "{:?} in answer to {}",
                String::from_utf8_lossy(reply),
                PROBE_REQUESTS[answered]
            );
            let listener = bind_private_socket(&fixture.path).expect("bind raw responder");
            let answered = served[..answered].to_vec();
            let server = spawn_ready_responder(move || {
                let (stream, _) = listener.accept().expect("accept the probe");
                answer_raw(stream, reply, &answered);
            });
            assert_eq!(probe(&fixture.path), want, "{label}");
            server.join().expect("raw responder joined");
            std::fs::remove_file(&fixture.path).expect("remove the responder's socket");
        }
    }

    /// TRUSTD-LOST-RACE-2: a lost race whose owner answers a line that is not
    /// exactly `ERR busy` ends at that first answer, refused, as before: it is
    /// asked once, and the wait ends after the release grace, well inside the
    /// window. The window is short so that a launcher that wrongly kept
    /// asking fails on its count, not on a 60 s wait. Positive control: the
    /// same owner answering exactly `ERR busy` is asked again until the
    /// deadline, so the harness can tell the two apart.
    #[test]
    fn a_lost_race_refuses_a_reply_that_is_not_exactly_busy_at_its_first_answer() {
        let window = Duration::from_secs(5);
        assert!(window > REFUSING_OWNER_RELEASE_GRACE + Duration::from_secs(2));
        for (reply, busy) in [
            (b"ERR busy\n".as_slice(), true),
            (b"ERR busyX\n", false),
            (b"ERR other\n", false),
            (b"garbage\n", false),
        ] {
            let label = String::from_utf8_lossy(reply).into_owned();
            let fixture = TestSocket::new("not-busy");
            let marker = fixture.path.with_file_name("loser-exited");
            let _cleanup = RemoveOnDrop(vec![marker.clone()]);
            let stop = Arc::new(AtomicBool::new(false));
            let owner = raw_owner(fixture.path.clone(), marker.clone(), reply, Arc::clone(&stop));
            let (child, stderr) = spawn_lost_race_loser(&marker);
            let expected = lost_race_identity('d');
            let timeout = Duration::from_millis(1500);
            let mut misses = Vec::new();
            let mut log = ProbeLog::default();
            let started = Instant::now();
            let error = wait_with_held_lock(child, stderr, timeout, window, |deadline| {
                log.record(deadline);
                let probe =
                    lease_compatible_daemon_probe_until(&fixture.path, &expected, deadline, || {
                        4096
                    });
                misses.push(probe.as_ref().err().copied());
                probe
            })
            .expect_err("no reply but a lease is ever adopted");
            let waited = started.elapsed();
            // Give a retrying launcher time to connect again before counting.
            thread::sleep(Duration::from_millis(300));
            stop.store(true, AtomicOrdering::SeqCst);
            let connections = owner.join().expect("raw owner joined");
            match error {
                EnsureDaemonError::EarlyExit { status, stderr, .. } => {
                    assert_eq!(status.code(), Some(1), "{label}");
                    assert!(stderr.contains(OWNED_ELSEWHERE), "{label}: {stderr}");
                }
                other => panic!("{label}: unexpected startup error: {other}"),
            }
            if busy {
                assert!(connections > 2, "{label}: asked again: {connections} connections");
                assert!(misses.contains(&Some(ProbeMiss::Busy)), "{label}: {misses:?}");
                assert!(waited >= window, "{label}: asked until the deadline: {waited:?}");
                continue;
            }
            // A probe of the still-running child may also reach the owner when
            // the loser stalls 300 ms or more between its marker and its exit
            // (it does under load), and that miss is ignored by design. So
            // count what the post-exit wait was answered, told apart by its
            // deadline as in [`ProbeLog`], not every connection.
            assert_eq!(log.0.len(), misses.len(), "{label}: one log entry per probe");
            let running_bound = log.0.first().expect("the wait probed").0 + timeout;
            let post_exit_answers = log
                .0
                .iter()
                .zip(&misses)
                .filter(|&(&(_, deadline), miss)| {
                    deadline > running_bound && *miss == Some(ProbeMiss::Refused)
                })
                .count();
            assert_eq!(
                post_exit_answers, 1,
                "{label}: refused at its first post-exit answer, never asked again: {misses:?}"
            );
            assert!(
                (1..=misses.len()).contains(&connections),
                "{label}: the owner was reached, and only by the wait's own probes: \
                 {connections} connections for {misses:?}"
            );
            assert_eq!(misses.last(), Some(&Some(ProbeMiss::Refused)), "{label}: {misses:?}");
            assert!(!misses.contains(&Some(ProbeMiss::Busy)), "{label}: {misses:?}");
            assert!(waited < window, "{label}: ended at the first answer: {waited:?}");
        }
    }

    /// TRUSTD-LOST-RACE-2 changes only the lost-race wait. The solver-launch
    /// path still refuses a selected daemon's `ERR busy` before any solver
    /// starts (fail-closed, nothing retried), while the lost-race probe reads
    /// the very same rejection as a capacity answer.
    #[test]
    fn err_busy_still_blocks_solver_launch_where_the_lost_race_probe_reads_capacity() {
        let identity = lost_race_identity('d');
        let fixture = TestSocket::new("busy-both");
        let daemon = Daemon::with_budget_and_identity(4096, identity.clone());
        let slots: Vec<_> = (0..MAX_SERVER_CONNECTIONS)
            .map(|_| daemon.try_acquire_connection().expect("fill a connection slot"))
            .collect();
        let listener = bind_private_socket(&fixture.path).expect("bind saturated responder");
        let saturated = Arc::clone(&daemon);
        let server = spawn_ready_responder(move || {
            for _ in 0..2 {
                let (stream, _) = listener.accept().expect("accept a client");
                let error = saturated.admit_connection(stream).err().expect("over the limit");
                assert_eq!(error.kind(), std::io::ErrorKind::WouldBlock, "{error}");
            }
        });
        let error =
            reserve_via_daemon_with(&fixture.path, 4096, "solver", TEST_OBSERVER_TIMEOUT, || {
                TEST_CLIENT_BUDGET
            })
            .expect_err("ERR busy from a selected daemon must block solver launch");
        assert!(error.to_string().contains("ERR busy"), "refused by the busy frame: {error}");
        assert_eq!(
            lease_compatible_daemon_probe_until(
                &fixture.path,
                &identity,
                Instant::now() + TEST_OBSERVER_TIMEOUT,
                || 4096
            )
            .err(),
            Some(ProbeMiss::Busy),
            "the lost-race probe reads the same rejection as capacity"
        );
        server.join().expect("saturated responder joined");
        drop(slots);
    }

    #[test]
    fn spawned_daemon_never_ready_has_an_absolute_timeout() {
        let (child, stderr) = spawn_readiness_fixture("sleep 1");
        let started = Instant::now();
        let error = wait_with_held_lock(
            child,
            stderr,
            Duration::from_millis(60),
            LIVE_OWNER_ADOPT_TIMEOUT,
            |_| Err::<(), _>(ProbeMiss::NotServing),
        )
        .expect_err("a live but never-ready child must time out");
        assert!(matches!(error, EnsureDaemonError::ReadinessTimeout { .. }));
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn trustd_executable_owner_policy_rejects_foreign_and_sticky_root_files() {
        let caller = 501;
        assert!(executable_owner_is_trusted(caller, caller, false));
        assert!(
            !executable_owner_is_trusted(caller, 502, false),
            "a foreign user's executable is never caller authority"
        );
        assert!(
            !executable_owner_is_trusted(caller, 0, false),
            "root ownership alone (including under a sticky parent) is insufficient"
        );
        assert!(
            executable_owner_is_trusted(caller, 0, true),
            "the narrow immutable system-tree exception admits root-owned tools"
        );

        let tmp = std::fs::canonicalize(std::env::temp_dir()).expect("canonical temp directory");
        assert!(
            !root_owned_immutable_system_parent(&tmp).expect("inspect temp directory"),
            "a shared/sticky temp tree is not an immutable system path"
        );
    }

    #[test]
    fn trustd_executable_identity_accepts_same_user_packaged_sibling() {
        let fixture = TestSocket::new("same-user-executable");
        let executable = fixture.path.parent().expect("fixture parent").join("trustd");
        std::fs::write(&executable, b"same-user packaged trustd").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700))
            .expect("make executable private");

        let identity = daemon_identity_for_executable(&executable)
            .expect("same-user executable in a private package directory is trusted");
        assert_eq!(identity.executable_sha256.len(), 64);
        std::fs::remove_file(executable).expect("remove executable fixture");
    }

    #[test]
    fn trustd_executable_identity_rejects_writable_ancestor_above_private_parent() {
        let fixture = TestSocket::new("writable-executable-ancestor");
        let root = fixture.path.parent().expect("fixture parent");
        let shared = root.join("shared");
        let package = shared.join("private-package");
        std::fs::create_dir(&shared).expect("create shared ancestor");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o700))
            .expect("make construction ancestor private");
        std::fs::create_dir(&package).expect("create private immediate parent");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o777))
            .expect("make ancestor cross-user writable");
        std::fs::set_permissions(&package, std::fs::Permissions::from_mode(0o700))
            .expect("keep immediate parent private");
        let executable = package.join("trustd");
        std::fs::write(&executable, b"untrusted ancestor trustd").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700))
            .expect("make executable private");

        let error = daemon_identity_for_executable(&executable)
            .expect_err("a private immediate parent cannot hide a writable ancestor");

        std::fs::remove_file(&executable).expect("remove executable fixture");
        std::fs::remove_dir(&package).expect("remove private package");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o700))
            .expect("restore shared ancestor for cleanup");
        std::fs::remove_dir(&shared).expect("remove shared ancestor");

        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        assert!(
            error.to_string().contains("executable ancestor"),
            "diagnostic names the full-chain authority failure: {error}"
        );
    }

    #[test]
    fn trustd_executable_canonical_path_eliminates_replaceable_alias_prefix() {
        use std::os::unix::fs::symlink;

        let fixture = TestSocket::new("canonical-executable-path");
        let root = fixture.path.parent().expect("fixture parent");
        let package = root.join("private-package");
        std::fs::create_dir(&package).expect("create package");
        std::fs::set_permissions(&package, std::fs::Permissions::from_mode(0o700))
            .expect("make package private");
        let executable = package.join("trustd");
        std::fs::write(&executable, b"canonical trustd").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700))
            .expect("make executable private");

        let shared = root.join("shared-aliases");
        std::fs::create_dir(&shared).expect("create alias ancestor");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o777))
            .expect("make alias ancestor replaceable");
        let alias = shared.join("package-link");
        symlink(&package, &alias).expect("create package alias");
        let through_alias = alias.join("trustd");

        let canonical = canonical_trusted_executable_path(&through_alias)
            .expect("the resolved target has a fully trusted ancestor chain");
        assert_eq!(
            canonical,
            std::fs::canonicalize(&executable).expect("canonical executable fixture")
        );
        assert!(
            !canonical.starts_with(&shared),
            "the path retained for hash/exec cannot traverse the replaceable alias ancestor"
        );

        std::fs::remove_file(&alias).expect("remove alias");
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o700))
            .expect("restore alias ancestor for cleanup");
        std::fs::remove_dir(&shared).expect("remove alias ancestor");
        std::fs::remove_file(&executable).expect("remove executable");
        std::fs::remove_dir(&package).expect("remove package");
    }

    #[test]
    fn trustd_executable_identity_accepts_immutable_root_system_binary() {
        let candidate =
            [Path::new("/usr/bin/true"), Path::new("/bin/true")].into_iter().find(|path| {
                std::fs::symlink_metadata(*path).is_ok_and(|metadata| {
                    metadata.file_type().is_file()
                        && metadata.uid() == 0
                        && metadata.permissions().mode() & 0o022 == 0
                })
            });
        if let Some(executable) = candidate {
            daemon_identity_for_executable(executable)
                .expect("immutable root-owned binary in a system tree is trusted");
        }
    }

    #[test]
    fn client_reservation_inert_when_no_socket() {
        // With SOCK env unset and TOKEN env unset, reserve is inert (rung 1).
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _socket = ScopedEnvOverride::remove(SOCK_ENV);
        let _token = ScopedEnvOverride::remove("TRUST_MEMORY_JOBSERVER");
        assert_eq!(default_reservation_bytes().expect("unconfigured default is available"), 0);
        let r = reserve(1024 * 1024).expect("unconfigured reservation is inert");
        assert!(!r.is_active(), "no socket + no token file ⇒ inert (drop-in)");
        drop(r);
    }

    #[test]
    fn zero_byte_client_reserve_is_inert() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _socket = ScopedEnvOverride::remove(SOCK_ENV);
        let _token = ScopedEnvOverride::remove("TRUST_MEMORY_JOBSERVER");
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let r = reserve(0).expect("zero-byte reservation is inert");
        assert!(!r.is_active());
        assert_eq!(r.bytes(), 0);
    }

    #[test]
    fn zero_byte_reserve_cannot_bypass_a_configured_unreachable_daemon() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let fixture = TestSocket::new("zero-unreachable");
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let error = reserve_labeled(0, "zero-unreachable")
            .expect_err("zero bytes must still validate the selected daemon authority");
        assert!(matches!(error, ReservationError::Daemon(_)));
    }

    #[test]
    fn empty_configured_socket_is_authoritative_and_fails_closed() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _socket = ScopedEnvOverride::set(SOCK_ENV, "");
        let _token = ScopedEnvOverride::remove("TRUST_MEMORY_JOBSERVER");
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);

        let default_error = default_reservation_bytes()
            .expect_err("empty socket configuration cannot derive an inert default");
        assert!(default_error.to_string().contains("configured with an empty path"));
        let reserve_error =
            reserve(0).expect_err("zero-byte admission cannot bypass an empty configured socket");
        assert!(reserve_error.to_string().contains("configured with an empty path"));
    }

    #[test]
    fn explicit_zero_byte_reserve_rejects_a_malformed_daemon() {
        let fixture = TestSocket::new("zero-malformed");
        let listener = UnixListener::bind(&fixture.path).expect("bind malformed zero responder");
        make_socket_private(&fixture.path);
        let server = spawn_ready_responder(move || {
            let (mut stream, _) = listener.accept().expect("accept zero-byte client");
            let mut request = String::new();
            BufReader::new(stream.try_clone().expect("clone malformed responder stream"))
                .read_line(&mut request)
                .expect("read STATUS preflight");
            assert_eq!(request, "STATUS\n", "zero-byte call must exercise authority");
            writeln!(stream, "{{\"version\":\"wrong\"}}").expect("write malformed STATUS response");
            stream.flush().expect("flush malformed STATUS response");
        });

        let error = reserve_labeled_at_with(
            &fixture.path,
            0,
            "zero-malformed",
            TEST_OBSERVER_TIMEOUT,
            || TEST_CLIENT_BUDGET,
        )
        .expect_err("explicit endpoint must validate even for zero bytes");
        // Name the refusal: a bare `Daemon(_)` also matches a deadline expiry,
        // so on a loaded host this test could pass without ever reaching the
        // malformed reply it exists to reject.
        assert!(
            matches!(&error, ReservationError::Daemon(message)
                if message.contains("invalid STATUS reply")),
            "the malformed reply is what is refused: {error}"
        );
        server.join().expect("malformed zero responder joined");
    }

    #[test]
    fn explicit_zero_byte_reserve_exercises_a_valid_daemon_then_returns_inert() {
        // The daemon's advertised ceiling and the client's acceptance check are
        // the SAME constant here. Reading `machine_budget_bytes()` for either
        // would put the process-global `BUDGET_BYTES_CACHE` between the two
        // observations, where a concurrently running sibling test's
        // `TestTotalMemory` injection can land and make this valid daemon look
        // unusable; `ENV_TEST_LOCK` cannot close that, because the cache has
        // writers that never take it. Two constants cannot race, and this test
        // is about the zero-byte protocol outcome, not about admission sizing.
        let fixture = TestSocket::new("zero-valid");
        let listener = UnixListener::bind(&fixture.path).expect("bind valid zero responder");
        make_socket_private(&fixture.path);
        let daemon = test_daemon(TEST_CLIENT_BUDGET);
        let server = spawn_ready_responder(move || {
            let (stream, _) = listener.accept().expect("accept valid zero-byte client");
            daemon.serve_conn(stream);
        });

        let reservation =
            reserve_labeled_at_with(&fixture.path, 0, "zero-valid", TEST_OBSERVER_TIMEOUT, || {
                TEST_CLIENT_BUDGET
            })
            .expect("valid selected daemon returns a sentinel");
        assert!(!reservation.is_active());
        assert_eq!(reservation.bytes(), 0);
        drop(reservation);
        server.join().expect("valid zero responder joined");
    }
}
