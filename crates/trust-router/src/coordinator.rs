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

// ===========================================================================
// Wire-protocol constants (single source of truth for client AND daemon)
// ===========================================================================

/// Environment variable naming the daemon's Unix-domain socket. The orchestrator
/// (`targo` crate mode) sets this to one private per-euid host endpoint shared
/// across Cargo target directories.
/// UNSET ⇒ rung 2 is skipped and the worker falls straight to the file bucket.
/// Additive/opt-in by presence: a worker built before this change ignores it.
pub const SOCK_ENV: &str = "TRUST_MEMORY_JOBSERVER_SOCK";

/// Force-skip daemon startup (debug/CI). When set to `1`, `ensure_daemon` is a
/// no-op. A caller may use the file lane only when no socket domain is also
/// configured; combining both fails closed to prevent split authority.
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

/// Idle-shutdown bound: if `active` is empty AND no admission-affecting request
/// has arrived for this long, the daemon exits so a `targo`-spawned daemon does
/// not outlive the build. Its socket remains as a stale rendezvous entry for the
/// next stable-lock owner to reclaim. Observational STATUS/PING/IDENTITY traffic
/// intentionally does not extend this lifetime.
pub(crate) const IDLE_TIMEOUT: Duration = Duration::from_secs(5 * 60);

/// Hard ceiling on live server connection threads. A normal build uses roughly
/// fourteen workers plus one observer; 64 leaves ample headroom without letting
/// same-euid clients turn one Unix socket into an unbounded thread allocator.
pub(crate) const MAX_SERVER_CONNECTIONS: usize = 64;

/// A newly accepted local client has ample time to send its first tiny frame,
/// but cannot occupy a handler indefinitely without speaking the protocol.
const SERVER_INITIAL_READ_TIMEOUT: Duration = Duration::from_secs(15);

/// Poll budget for `ensure_daemon` readiness after spawning `trustd`.
const SPAWN_READY_TIMEOUT: Duration = Duration::from_millis(500);
/// Per-poll connect-attempt spacing while waiting for `trustd` to bind.
const SPAWN_POLL_INTERVAL: Duration = Duration::from_millis(20);

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
}

/// The mutable budget state, guarded by [`Daemon::state`].
#[derive(Debug)]
pub(crate) struct Budget {
    budget_bytes: u64,
    reserved_bytes: u64,
    active: Vec<ServerReservation>,
    /// Monotonic token allocator. Starts at 1 (`0` = inert sentinel).
    next_token: u64,
    granted_total: u64,
    released_total: u64,
    /// Parked RESERVE waiters.
    queue_depth: u64,
    started_at: u64,
}

impl Budget {
    fn new(budget_bytes: u64) -> Self {
        Self {
            budget_bytes,
            reserved_bytes: 0,
            active: Vec::new(),
            next_token: 1,
            granted_total: 0,
            released_total: 0,
            queue_depth: 0,
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

    /// Whether the daemon has been idle (no live reservations and no
    /// admission-affecting request) long enough to self-shut-down.
    pub(crate) fn idle_expired(&self) -> bool {
        let st = self.lock();
        if !st.active.is_empty() || st.queue_depth != 0 {
            return false;
        }
        drop(st);
        let last = *self.last_activity.lock().unwrap_or_else(|e| e.into_inner());
        unix_now().saturating_sub(last) >= IDLE_TIMEOUT.as_secs()
    }

    /// Atomically close admission once the idle deadline has elapsed and the
    /// authoritative ledger has no grants or waiters. Holding the ledger lock
    /// across the flag transition prevents a RESERVE from racing between the
    /// empty-state proof and shutdown. The flag is irreversible for this daemon
    /// instance; after it is set, the listener may durably record CLEAN.
    fn try_begin_idle_shutdown(&self) -> bool {
        let st = self.lock();
        if !st.active.is_empty() || st.queue_depth != 0 {
            return false;
        }
        let last = *self.last_activity.lock().unwrap_or_else(|e| e.into_inner());
        if unix_now().saturating_sub(last) < IDLE_TIMEOUT.as_secs() {
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
        if self.shutting_down.load(AtomicOrdering::Acquire) {
            return "DEGRADED".to_string();
        }
        // `RESERVE 0` is inert: hand back sentinel token 0 (RELEASE 0 no-ops),
        // mirroring `acquire(0)`. Not counted in granted_total.
        if bytes == 0 {
            return "GRANTED 0".to_string();
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
                return "DEGRADED".to_string();
            }
            // Impossible request (cannot ever fit) or disabled budget ⇒ immediate
            // DEGRADED, never park. Mirrors the file bucket's early-return.
            if st.budget_bytes == 0 || bytes > st.budget_bytes {
                return "DEGRADED".to_string();
            }
            if st.reserved_bytes.saturating_add(bytes) <= st.budget_bytes {
                let token = st.next_token;
                // Advance, skipping 0 (the inert sentinel) on the wrap.
                st.next_token = st.next_token.wrapping_add(1).max(1);
                st.active.push(ServerReservation {
                    token,
                    pid,
                    bytes,
                    label,
                    granted_at: Instant::now(),
                });
                st.reserved_bytes = st.reserved_bytes.saturating_add(bytes);
                st.granted_total = st.granted_total.saturating_add(1);
                return format!("GRANTED {token}");
            }
            // Does not fit yet: park until a peer releases or the deadline lapses.
            let elapsed = start.elapsed();
            if elapsed >= deadline {
                return "DEGRADED".to_string();
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
        // its live owner still holds the reservation.
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
            let reply = if requests_nonzero_grant && connection_grants.has_live_grant() {
                // The normal client protocol needs exactly one reservation per
                // connection. Bounding that ownership state prevents one
                // authenticated peer from filling the heap/STATUS document with
                // millions of one-byte grants despite the connection cap.
                self.touch_activity();
                "ERR outstanding-grant".to_string()
            } else if requested_release
                .is_some_and(|token| token != 0 && !connection_grants.contains(token))
            {
                // Tokens are visible in STATUS for diagnostics, so knowledge is
                // not authority. Only the connection that received a live grant
                // may return it; otherwise one client could undercount another
                // worker and cause unsafe over-admission.
                self.touch_activity();
                "ERR unowned-token".to_string()
            } else {
                self.handle_line(&line)
            };
            if let Some(token) = reply
                .strip_prefix("GRANTED ")
                .and_then(|token| token.trim().parse::<u64>().ok())
                .filter(|token| *token != 0)
            {
                // Record before writing the reply: if the peer disappears while
                // the frame is sent, connection cleanup still returns the grant.
                connection_grants.insert(token);
            }
            if reply == "OK"
                && let Some(token) = requested_release
            {
                connection_grants.remove(token);
            }
            if writeln!(writer, "{reply}").is_err() || writer.flush().is_err() {
                break;
            }
            // Only a live connection-owned grant may clear the idle timeout.
            // A successful RELEASE removes that authority above, so reset the
            // ordinary client timeout immediately instead of letting an idle
            // post-release peer retain one handler forever.
            let next_read_timeout = if connection_grants.has_live_grant() {
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

#[cfg(unix)]
fn reject_busy_connection(mut stream: UnixStream) -> std::io::Result<()> {
    stream.set_write_timeout(Some(OBSERVER_IO_TIMEOUT))?;
    stream.write_all(b"ERR busy\n")?;
    stream.flush()?;
    stream.shutdown(std::net::Shutdown::Write)?;

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
        stream.set_read_timeout(Some(remaining))?;
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
        Ok(metadata)
            if metadata.file_type().is_socket()
                && metadata.uid() == unsafe { libc::geteuid() }
                && metadata.permissions().mode() & 0o077 == 0 =>
        {
            Ok(Some(socket_identity(&metadata)))
        }
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
/// A second process can observe the brand-new sentinel between `O_EXCL` file
/// creation and the creator taking its flock. Give that creator one short,
/// bounded scheduling window to initialize the record and acquire ownership.
/// A genuinely torn crash record remains fail-closed after this grace period.
#[cfg(unix)]
const STABLE_EPOCH_INITIALIZATION_GRACE: Duration = Duration::from_millis(50);

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
fn open_stable_ownership_lock(
    canonical_socket: &Path,
) -> std::io::Result<(StableOwnershipLock, StableEpoch)> {
    let path = stable_lock_path_for_socket(canonical_socket)?;
    let options = || {
        let mut options = OpenOptions::new();
        options
            .truncate(false)
            .read(true)
            .write(true)
            .mode(0o600)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
        options
    };
    let (file, newly_created) = match options().create_new(true).open(&path) {
        Ok(file) => (file, true),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            (options().open(&path)?, false)
        }
        Err(error) => return Err(error),
    };
    let metadata = file.metadata()?;
    let euid = unsafe { libc::geteuid() };
    if !metadata.file_type().is_file()
        || metadata.uid() != euid
        || metadata.permissions().mode() & 0o077 != 0
        || metadata.nlink() != 1
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            format!("invalid trustd ownership sentinel: {}", path.display()),
        ));
    }

    let result = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
    if result != 0 {
        let error = std::io::Error::last_os_error();
        let raw = error.raw_os_error();
        if raw == Some(libc::EWOULDBLOCK) || raw == Some(libc::EAGAIN) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::AddrInUse,
                format!("another trustd owns {}", canonical_socket.display()),
            ));
        }
        return Err(error);
    }
    let ownership = StableOwnershipLock { file, path };
    if newly_created {
        // Empty or torn records are never interpreted as clean. Initialize a
        // brand-new sentinel under its kernel lock, sync the inode, then sync
        // the containing directory so the rendezvous survives a system crash.
        ownership.mark_clean()?;
        let parent = ownership.path.parent().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("ownership sentinel has no parent: {}", ownership.path.display()),
            )
        })?;
        File::open(parent)?.sync_all()?;
    }
    let epoch = ownership.epoch()?;
    Ok((ownership, epoch))
}

#[cfg(unix)]
fn try_stable_ownership_lock(canonical_socket: &Path) -> std::io::Result<StableOwnershipLock> {
    let initialization_deadline =
        Instant::now().checked_add(STABLE_EPOCH_INITIALIZATION_GRACE).unwrap_or_else(Instant::now);
    loop {
        let (ownership, epoch) = open_stable_ownership_lock(canonical_socket)?;
        if epoch == StableEpoch::Clean {
            return Ok(ownership);
        }
        if epoch == StableEpoch::Invalid && Instant::now() < initialization_deadline {
            // Do not retain the flock while waiting: the exclusive creator that
            // published the empty inode must be able to initialize it and take
            // ownership. Its subsequent flock makes our next attempt report
            // AddrInUse. A crashed creator never changes the record, so the
            // absolute deadline still requires explicit recovery.
            drop(ownership);
            let remaining = initialization_deadline.saturating_duration_since(Instant::now());
            thread::sleep(remaining.min(Duration::from_millis(1)));
            continue;
        }
        return Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!(
                "trustd crash epoch is not CLEAN for {}; automatic restart is refused because a prior solver may still hold memory. Establish every solver from the prior daemon is gone, then invoke `/absolute/path/to/selected/sysroot/bin/trustd --recover-after-crash --confirm-no-solvers --socket {}`: derive that absolute trustd as the same-sysroot sibling of the selected, validated Targo, never from ambient PATH. The path relation does not itself prove packaged byte or execution identity; the confirmation is an operator attestation, not a process check, so reboot first if uncertain",
                canonical_socket.display(),
                canonical_socket.display(),
            ),
        ));
    }
}

/// A bound endpoint plus the external advisory lock proving this process is its
/// sole daemon owner. Dropping it closes the listener and releases the kernel
/// lock, but intentionally leaves both socket and lock sentinel for the next
/// locked owner to classify/reclaim.
#[cfg(unix)]
struct OwnedSocket {
    listener: UnixListener,
    #[cfg(test)]
    identity: SocketIdentity,
    ownership_lock: StableOwnershipLock,
}

#[cfg(unix)]
impl OwnedSocket {
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
#[cfg(unix)]
fn connect_unix_until(path: &Path, deadline: Instant) -> std::io::Result<UnixStream> {
    let raw_fd = unsafe { libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0) };
    if raw_fd < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let owned = unsafe { OwnedFd::from_raw_fd(raw_fd) };

    let descriptor_flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFD) };
    if descriptor_flags < 0
        || unsafe {
            libc::fcntl(owned.as_raw_fd(), libc::F_SETFD, descriptor_flags | libc::FD_CLOEXEC)
        } < 0
    {
        return Err(std::io::Error::last_os_error());
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

#[cfg(unix)]
fn connect_trusted_until(path: &Path, deadline: Instant) -> std::io::Result<UnixStream> {
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

    // No request can reach the listener before this function returns. Persist
    // DIRTY first so SIGKILL/OOM at any later point cannot permit an empty-ledger
    // replacement daemon while an already-admitted solver is still alive.
    ownership_lock.mark_dirty()?;

    Ok(OwnedSocket {
        listener,
        #[cfg(test)]
        identity,
        ownership_lock,
    })
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

/// Bind the daemon to `sock` and serve until a proven-quiescent idle shutdown.
/// A stable per-socket lock and durable DIRTY epoch are held for the complete
/// lifetime. Only the admission-closed, empty-ledger shutdown path writes CLEAN;
/// errors, aborts, OOM, and SIGKILL therefore make automatic restart fail closed.
/// Normal shutdown never unlinks the endpoint; the next locked owner reclaims it.
#[cfg(unix)]
pub fn serve(sock: &Path) -> std::io::Result<()> {
    let identity = runtime_daemon_identity()?;
    let owned = bind_owned_socket(sock)?;
    let daemon = Daemon::new(identity);

    // The accept loop owns the clean transition. Keeping refresh, the idle proof,
    // admission closure, and epoch sync in this thread avoids process::exit from
    // a maintenance thread bypassing the durable shutdown protocol.
    owned.listener.set_nonblocking(true)?;
    let mut next_refresh =
        Instant::now().checked_add(BUDGET_REFRESH_INTERVAL).unwrap_or_else(Instant::now);
    loop {
        let now = Instant::now();
        if now >= next_refresh {
            daemon.refresh_budget_ceiling();
            next_refresh = now.checked_add(BUDGET_REFRESH_INTERVAL).unwrap_or_else(Instant::now);
            if daemon.try_begin_idle_shutdown() {
                owned.mark_clean()?;
                return Ok(());
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
    pub(crate) fn configure_child_lifetime_guard(
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
    ConfiguredDaemonAttempt::Selected(reserve_via_daemon(&sock, bytes, label))
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
    let status_deadline =
        Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until(sock, status_deadline).map_err(|error| {
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
    let client_budget = machine_budget_bytes();
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
        let _ = stream.set_write_timeout(Some(OBSERVER_IO_TIMEOUT));
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
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until(sock, deadline).ok()?;
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
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until(sock, deadline).ok()?;
    write_line_until(&mut stream, "IDENTITY", deadline).ok()?;
    let line = read_one_line_until(&stream, deadline)?;
    let identity: DaemonIdentity = serde_json::from_str(line.trim()).ok()?;
    identity.has_valid_invariants().then_some(identity)
}

#[cfg(unix)]
fn compatible_daemon_at(sock: &Path, expected: &DaemonIdentity) -> bool {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    compatible_daemon_until(sock, expected, deadline)
}

#[cfg(unix)]
fn compatible_daemon_until(sock: &Path, expected: &DaemonIdentity, deadline: Instant) -> bool {
    compatible_daemon_until_with_budget_source(sock, expected, deadline, machine_budget_bytes)
}

#[cfg(unix)]
fn compatible_daemon_until_with_budget_source<F>(
    sock: &Path,
    expected: &DaemonIdentity,
    deadline: Instant,
    current_client_budget: F,
) -> bool
where
    F: FnOnce() -> u64,
{
    let Ok(mut stream) = connect_trusted_until(sock, deadline) else {
        return false;
    };
    if write_line_until(&mut stream, "IDENTITY", deadline).is_err() {
        return false;
    }
    let Some(identity_line) = read_one_line_until(&stream, deadline) else {
        return false;
    };
    let Ok(identity) = serde_json::from_str::<DaemonIdentity>(identity_line.trim()) else {
        return false;
    };
    if !identity.has_valid_invariants() || &identity != expected {
        return false;
    }

    if write_line_until(&mut stream, "STATUS", deadline).is_err() {
        return false;
    }
    let Some(status_line) = read_one_line_until(&stream, deadline) else {
        return false;
    };
    let Ok(status) = serde_json::from_str::<DaemonStatus>(status_line.trim()) else {
        return false;
    };
    // Observe after the protocol exchange so a recently lowered cgroup ceiling
    // is compared as late as practical before adopting this daemon.
    daemon_budget_is_acceptable(&status, current_client_budget())
}

/// Return whether `sock` is a healthy daemon running the exact bytes and build
/// identity at `executable`. `ensure_daemon` uses the same check for its packaged
/// sibling; the explicit form is useful to release diagnostics and contract
/// tests without consulting PATH.
#[must_use]
#[cfg(unix)]
pub fn daemon_matches_executable(sock: &Path, executable: &Path) -> bool {
    daemon_identity_for_executable(executable)
        .is_ok_and(|expected| compatible_daemon_at(sock, &expected))
}

/// Best-effort: ensure a compatible daemon is listening on `sock`. Readiness
/// requires both exact packaged-binary [`DaemonIdentity`] and a semantically
/// valid [`STATUS_VERSION`] response, not merely a `PONG` from an arbitrary
/// process. Otherwise spawn the packaged `trustd` and identity/status-poll for
/// readiness up to [`SPAWN_READY_TIMEOUT`]. Returns `false` on failure; a caller
/// that has provisioned this socket domain must not silently launch workers on
/// an independent file authority. No-op when [`DISABLE_ENV`] is set.
#[cfg(unix)]
pub fn ensure_daemon(sock: &Path) -> bool {
    if disabled() {
        return false;
    }
    // Resolve only the trustd packaged beside this executable. An ambient
    // CARGO_HOME/PATH daemon is not part of this toolchain's authenticated
    // identity and must never become its memory-budget authority.
    let Some((trustd, expected_identity)) = resolve_trustd() else {
        return false;
    };
    // Resolve and hash the exact packaged sibling before accepting any existing
    // endpoint. STATUS compatibility alone is intentionally insufficient.
    if compatible_daemon_at(sock, &expected_identity) {
        return true;
    }
    // Spawn without inherited stdio. A tiny waiter thread owns the Child handle
    // so idle exit cannot leave a zombie in a long-lived launcher process.
    let mut command = std::process::Command::new(&trustd);
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
        .stderr(std::process::Stdio::null());
    let Ok(mut child) = command.spawn() else {
        return false;
    };
    thread::spawn(move || {
        let _ = child.wait();
    });
    // IDENTITY + STATUS poll for readiness. This checks executable bytes, build
    // provenance, transport, protocol, closed schemas, and budget invariants.
    let ready_deadline =
        Instant::now().checked_add(SPAWN_READY_TIMEOUT).unwrap_or_else(Instant::now);
    while Instant::now() < ready_deadline {
        if compatible_daemon_until(sock, &expected_identity, ready_deadline) {
            return true;
        }
        let remaining = ready_deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            break;
        }
        thread::sleep(SPAWN_POLL_INTERVAL.min(remaining));
    }
    false
}

/// Bounded liveness probe against an explicit trusted endpoint; `true` iff it
/// replies with exactly `PONG` before the observer deadline.
#[must_use]
#[cfg(unix)]
pub fn ping_at(sock: &Path) -> bool {
    let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
    let Ok(mut stream) = connect_trusted_until(sock, deadline) else {
        return false;
    };
    if write_line_until(&mut stream, "PING", deadline).is_err() {
        return false;
    }
    matches!(read_one_line_until(&stream, deadline), Some(l) if l.trim() == "PONG")
}

/// Exercise the complete release-diagnostic protocol against an endpoint that
/// must identify as the exact bytes at `expected_executable`.
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
    const SMOKE_BYTES: u64 = 1;

    if label.is_empty() || label.len() > MAX_LABEL_BYTES || label.contains(['\n', '\r']) {
        return Err(
            "daemon smoke label must be non-empty, single-line, and within the protocol bound"
                .to_string(),
        );
    }
    if !daemon_matches_executable(sock, expected_executable) {
        return Err("daemon endpoint does not match the exact expected executable".to_string());
    }
    if !ping_at(sock) {
        return Err("daemon did not answer PING with PONG".to_string());
    }
    let identity = identity_at(sock)
        .ok_or_else(|| "daemon did not return a valid closed IDENTITY response".to_string())?;
    let before = status_at(sock)
        .ok_or_else(|| "daemon did not return a valid initial STATUS response".to_string())?;
    if before.reserved_bytes != 0 || !before.active.is_empty() {
        return Err("daemon smoke requires an initially empty reservation state".to_string());
    }

    let reservation = reserve_labeled_at(sock, SMOKE_BYTES, label)
        .map_err(|error| format!("daemon did not grant the smoke RESERVE request: {error}"))?;
    if !reservation.is_active() || reservation.bytes() != SMOKE_BYTES {
        return Err("daemon did not grant one active smoke reservation byte".to_string());
    }
    let reserved = status_at(sock)
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
        let status = status_at(sock)
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
    if !daemon_matches_executable(sock, expected_executable) {
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
fn resolve_trustd() -> Option<(PathBuf, DaemonIdentity)> {
    let candidate = resolve_trustd_sibling(&std::env::current_exe().ok()?)?;
    // Return the same canonical, full-ancestor-authorized path that identity
    // hashing consumes. `ensure_daemon` must never hash one pathname and exec a
    // second traversal through a replaceable symlink/ancestor.
    let path = canonical_trusted_executable_path(&candidate).ok()?;
    let identity = daemon_identity_for_executable(&path).ok()?;
    Some((path, identity))
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
                if buf.len() >= MAX_REQUEST_BYTES * 64 {
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
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

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
            // File-ledger authority deliberately rejects shared/sticky
            // ancestors such as /tmp. Place this fixture below the checkout,
            // whose euid/root-owned chain matches the accepted production shape.
            let directory = std::env::current_dir().expect("test working directory").join(format!(
                ".trust-file-lane-test-{label}-{}-{nonce:x}-{sequence}",
                std::process::id()
            ));
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
            !compatible_daemon_at(&fixture.path, &expected),
            "STATUS v1 compatibility cannot override a mismatched executable hash"
        );
        server.join().expect("wrong identity server joined");
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
        assert!(
            !compatible_daemon_until_with_budget_source(&fixture.path, &identity, deadline, || {
                1024
            },),
            "a narrower client must not adopt a broader daemon ceiling"
        );
        let deadline = Instant::now().checked_add(OBSERVER_IO_TIMEOUT).unwrap_or_else(Instant::now);
        assert!(
            compatible_daemon_until_with_budget_source(&fixture.path, &identity, deadline, || 4096,),
            "an equal client budget may adopt the exact daemon"
        );
        server.join().expect("broader-cgroup server joined");
    }

    #[test]
    fn configured_hung_daemon_fails_without_minting_file_capacity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
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
        let server = thread::spawn(move || {
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
        let fixture = TestSocket::new("malformed-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind malformed responder");
        make_socket_private(&fixture.path);
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let file_lane = TestFileLane::new("malformed");
        file_lane.prove_lane_would_grant_then_reset(4096);

        let (stop_tx, stop_rx) = std::sync::mpsc::channel();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("accept reserve client");
            let request = read_one_line(&stream).expect("read STATUS frame");
            assert_eq!(request, "STATUS");
            writeln!(stream, "NOT-A-RESERVATION").expect("write malformed response");
            stream.flush().expect("flush malformed response");
            let _ = stop_rx.recv();
        });

        let error = reserve_labeled(4096, "malformed")
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
        let fixture = TestSocket::new("declined-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind declining responder");
        make_socket_private(&fixture.path);
        let _socket = ScopedEnvOverride::set(SOCK_ENV, &fixture.path);
        let _enabled = ScopedEnvOverride::remove(DISABLE_ENV);
        let file_lane = TestFileLane::new("declined");
        file_lane.prove_lane_would_grant_then_reset(4096);

        let daemon = test_daemon(1024);
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept declined reserve client");
            daemon.serve_conn(stream);
        });

        let error = reserve_labeled(4096, "too-large")
            .expect_err("DEGRADED from a selected daemon must block solver launch");
        assert!(error.to_string().contains("declined the reservation"));
        file_lane.assert_no_token_minted();
        server.join().expect("declining responder joined");
    }

    #[test]
    fn configured_over_connection_limit_fails_without_minting_file_capacity() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
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
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept over-limit client");
            let error = daemon
                .admit_connection(stream)
                .err()
                .expect("the sixty-fifth connection is rejected");
            assert_eq!(error.kind(), std::io::ErrorKind::WouldBlock);
            drop(permits);
        });

        let error = reserve_labeled(4096, "sixty-fifth")
            .expect_err("ERR busy from a selected daemon must block solver launch");
        assert!(error.to_string().contains("ERR busy"));
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

        let mut command = std::process::Command::new("/bin/sleep");
        command.arg("0.25");
        inherit_fd_across_exec(&mut command, client.as_raw_fd())
            .expect("retain child guard descriptor");
        let mut child = command.spawn().expect("spawn child with inherited guard fd");
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

        child.wait().expect("wait guarded child");
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
        let mut command = std::process::Command::new("/bin/sleep");
        command.arg("0.25");
        reservation
            .configure_child_lifetime_guard(&mut command)
            .expect("Command takes structural ownership of a stable descriptor");

        drop(reservation);
        assert_eq!(
            d.lock().reserved_bytes,
            4096,
            "dropping Reservation cannot close the Command-owned connection"
        );
        let mut child = command.spawn().expect("spawn after Reservation drop");
        drop(command);
        thread::sleep(Duration::from_millis(50));
        assert_eq!(d.lock().reserved_bytes, 4096, "child inherited the stable descriptor");

        child.wait().expect("wait guarded child");
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
        let mut command = std::process::Command::new("/bin/sh");
        command
            .args(["-c", "(sleep 0.35) & exit 0"])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        reservation.configure_child_lifetime_guard(&mut command).expect("install child EOF guard");
        let mut leader = command.spawn().expect("spawn solver leader and descendant");
        drop(command);
        leader.wait().expect("reap exited leader");

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

        handler.join().expect("handler observes descendant's final EOF");
        let state = d.lock();
        assert_eq!(state.reserved_bytes, 0);
        assert!(state.active.is_empty());
        assert_eq!(state.released_total, 1);
    }

    #[test]
    fn active_file_reservation_refuses_external_child_spawn() {
        let _guard = memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
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
        let fixture = TestSocket::new("explicit-reserve");
        let listener = UnixListener::bind(&fixture.path).expect("bind explicit reserve server");
        make_socket_private(&fixture.path);
        let daemon = test_daemon(64 << 10);
        let observed = Arc::clone(&daemon);
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept explicit reserve client");
            daemon.serve_conn(stream);
        });

        let reservation =
            reserve_labeled_at(&fixture.path, 4096, "release-proof").expect("daemon reply");
        assert!(reservation.is_active());
        assert_eq!(reservation.bytes(), 4096);
        assert_eq!(observed.lock().reserved_bytes, 4096);
        release(reservation);
        server.join().expect("explicit reserve server joined");
        assert_eq!(observed.lock().reserved_bytes, 0);
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
        assert!(UnixStream::connect(&fixture.path).is_err(), "stale socket has no listener");

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
        let owner = bind_owned_socket(&fixture.path).expect("first owner binds and marks DIRTY");
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
    fn torn_epoch_remains_fail_closed_after_bounded_initialization_grace() {
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
            "initialization grace must remain absolutely bounded"
        );

        assert!(
            recover_dirty_epoch_after_quiescence(&fixture.path)
                .expect("explicit recovery repairs the torn epoch")
        );
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
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("accept zero-byte client");
            let mut request = String::new();
            BufReader::new(stream.try_clone().expect("clone malformed responder stream"))
                .read_line(&mut request)
                .expect("read STATUS preflight");
            assert_eq!(request, "STATUS\n", "zero-byte call must exercise authority");
            writeln!(stream, "{{\"version\":\"wrong\"}}").expect("write malformed STATUS response");
            stream.flush().expect("flush malformed STATUS response");
        });

        let error = reserve_labeled_at(&fixture.path, 0, "zero-malformed")
            .expect_err("explicit endpoint must validate even for zero bytes");
        assert!(matches!(error, ReservationError::Daemon(_)));
        server.join().expect("malformed zero responder joined");
    }

    #[test]
    fn explicit_zero_byte_reserve_exercises_a_valid_daemon_then_returns_inert() {
        let budget = machine_budget_bytes();
        if budget == 0 {
            return;
        }
        let fixture = TestSocket::new("zero-valid");
        let listener = UnixListener::bind(&fixture.path).expect("bind valid zero responder");
        make_socket_private(&fixture.path);
        let daemon = test_daemon(budget);
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().expect("accept valid zero-byte client");
            daemon.serve_conn(stream);
        });

        let reservation = reserve_labeled_at(&fixture.path, 0, "zero-valid")
            .expect("valid selected daemon returns a sentinel");
        assert!(!reservation.is_active());
        assert_eq!(reservation.bytes(), 0);
        drop(reservation);
        server.join().expect("valid zero responder joined");
    }
}
