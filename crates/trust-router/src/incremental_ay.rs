// trust-router/incremental_ay.rs: Incremental AY session with push/pop scoping
//
// Provides IncrementalAYSession that maintains a persistent ay
// solver context across multiple VC verifications. Common assertions (type
// constraints, shared variable declarations) are asserted once at the base
// scope level. Per-VC assertions use push/pop to create isolated scopes while
// reusing the base context and learned lemmas.
//
// This module uses the ay-bindings typed API (AYProgram, Expr, Sort) for
// type-safe constraint construction, then serializes to SMT-LIB2 and
// dispatches via the persistent solver subprocess with incremental protocol.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::{Read as _, Write as _};
use std::process::{Child, Command, Stdio};
use std::sync::{Mutex, mpsc};
use std::time::{Duration, Instant};

use trust_types::*;

use crate::error::SolverProcessError;
use crate::{BackendRole, VerificationBackend, smt2_export, smtlib_backend};

/// Default timeout per-query in milliseconds.
const DEFAULT_QUERY_TIMEOUT_MS: u64 = 30_000;

/// Maximum consecutive failures before permanently falling back.
const MAX_CONSECUTIVE_FAILURES: u32 = 3;

/// Maximum model output size in bytes (10 MiB).
const MAX_MODEL_OUTPUT_BYTES: usize = 10 * 1024 * 1024;

const PRE_SPAWN_ADMISSION_PREFIX: &str = "memory admission failed before solver spawn:";
const PRE_SPAWN_LIFETIME_PREFIX: &str =
    "memory admission could not bind solver lifetime before spawn:";

/// Admission and authority configuration failures happen before a solver
/// exists. Retrying them through the one-shot fallback would repeat the same
/// potentially long admission wait, miscount an infrastructure outage as a
/// solver crash, and could eventually poison the session into permanent
/// fallback. Keep this classification narrow and tied to the two pre-spawn
/// boundaries that deliberately add these stable prefixes.
fn is_pre_spawn_admission_error(error: &str) -> bool {
    error.starts_with(PRE_SPAWN_ADMISSION_PREFIX) || error.starts_with(PRE_SPAWN_LIFETIME_PREFIX)
}

/// Statistics for an incremental AY session.
#[derive(Debug, Clone, Default)]
pub struct IncrementalAYStats {
    /// Total VCs verified through this session.
    pub total_queries: u64,
    /// VCs verified using shared context (incremental path).
    pub incremental_queries: u64,
    /// VCs that fell back to per-process mode.
    pub fallback_queries: u64,
    /// Number of solver process restarts.
    pub restarts: u64,
    /// Whether the session permanently fell back to per-process mode.
    pub permanently_fallen_back: bool,
    /// Number of common assertions shared across VCs.
    pub common_assertions: usize,
    /// Cumulative time saved (estimated) by reusing shared context (ms).
    pub estimated_time_saved_ms: u64,
}

/// Internal state of the persistent solver process.
struct SolverProcess {
    child: Child,
    /// True only when this module configured a fresh process group before exec.
    /// Tests may construct a protocol fixture around an ordinary child.
    group_isolated: bool,
    stdin: std::process::ChildStdin,
    /// Channel receiver for lines read by the dedicated reader thread.
    line_rx: mpsc::Receiver<Result<String, String>>,
    /// Aggregate-memory reservation held for the lifetime of this solver
    /// process. Released to the cross-process budget when the process is
    /// dropped/killed (RAII), so the budget a long-lived incremental session
    /// holds is freed exactly when its `ay` exits. Inert when no coordinator is
    /// active (drop-in standalone behavior).
    ///
    // Trust: routed through `coordinator::Reservation`. The daemon lane is used
    // when its socket is configured; the file lane is eligible only when no
    // socket lane was provisioned. A selected authority failure returns before
    // solver spawn instead of crossing ledgers or launching unreserved.
    _reservation: crate::coordinator::Reservation,
}

impl Drop for SolverProcess {
    fn drop(&mut self) {
        // Reservation is a field and therefore drops only after this destructor.
        // Kill the complete solver process group and reap its leader first, so a
        // timeout/error/panic cannot return aggregate capacity while `ay` (or a
        // same-group helper it spawned) is still consuming memory.
        terminate_solver_process_group(&mut self.child, self.group_isolated);
    }
}

/// One-shot solver leader paired with the reservation that authorized it.
/// `reaped` avoids signalling a process-group ID after a normally exited leader
/// has already been reaped and its numeric PID could be reused.
struct ReservedSolverChild {
    child: Child,
    _reservation: crate::coordinator::Reservation,
    group_isolated: bool,
    reaped: bool,
}

impl ReservedSolverChild {
    fn new(
        child: Child,
        reservation: crate::coordinator::Reservation,
        group_isolated: bool,
    ) -> Self {
        Self { child, _reservation: reservation, group_isolated, reaped: false }
    }

    /// Observe leader exit without releasing its PID/PGID reservation on Unix.
    /// This lets cleanup kill same-group helpers before `wait()` makes the
    /// numeric process-group ID reusable.
    fn exited_without_reaping(&mut self) -> std::io::Result<bool> {
        #[cfg(unix)]
        {
            let pid = i32::try_from(self.child.id()).map_err(|_| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "solver pid does not fit platform pid_t",
                )
            })?;
            let mut exit_info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
            let observed = unsafe {
                libc::waitid(
                    libc::P_PID,
                    pid as libc::id_t,
                    exit_info.as_mut_ptr(),
                    libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
                )
            };
            if observed < 0 {
                return Err(std::io::Error::last_os_error());
            }
            let exit_info = unsafe { exit_info.assume_init() };
            Ok(unsafe { exit_info.si_pid() } == pid)
        }
        #[cfg(not(unix))]
        {
            let exited = self.child.try_wait()?.is_some();
            self.reaped |= exited;
            Ok(exited)
        }
    }

    fn terminate_and_reap(&mut self) {
        if !self.reaped {
            terminate_solver_process_group(&mut self.child, self.group_isolated);
            self.reaped = true;
        }
    }
}

impl Drop for ReservedSolverChild {
    fn drop(&mut self) {
        self.terminate_and_reap();
    }
}

/// Put each solver in a fresh process group before `exec`. This is a normal
/// `posix_spawn` attribute on supported Unix targets, not an after-spawn race.
fn isolate_solver_process_group(command: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }
}

/// Terminate the isolated solver group, then reap its direct child leader.
/// Non-Unix standalone builds have only the portable direct-child primitive;
/// verified crate mode already rejects those platforms before fan-out.
fn terminate_solver_process_group(child: &mut Child, group_isolated: bool) {
    #[cfg(unix)]
    {
        if group_isolated && let Ok(pid) = i32::try_from(child.id()) {
            // Negative PID addresses the process group created before exec.
            let _ = unsafe { libc::kill(-pid, libc::SIGKILL) };
        }
    }
    #[cfg(not(unix))]
    let _ = group_isolated;
    // Fallback/direct-leader guarantee, and the portable non-Unix behavior.
    let _ = child.kill();
    let _ = child.wait();
}

/// Mutable session state protected by a Mutex for `Sync` compliance.
///
/// Follows the same pattern as `IncrementalSmtLibBackend`: mutable state
/// (solver process, failure counters) is behind a Mutex, while immutable
/// configuration (solver path, args, common assertions) stays in the outer
/// struct. This allows `VerificationBackend` (which requires `Sync`) to be
/// implemented without wrapping the entire struct.
struct SessionState {
    /// The live solver process.
    process: Option<SolverProcess>,
    /// Whether common assertions have been sent to the current process.
    base_initialized: bool,
    /// Number of consecutive process failures.
    consecutive_failures: u32,
    /// Whether permanently fallen back to per-process mode.
    fallen_back: bool,
    /// Session statistics.
    stats: IncrementalAYStats,
    /// Trust: The per-function shared assertion prefix currently installed at
    /// the solver's BASE scope (outside any push/pop), in addition to the
    /// static `common_assertions`. `verify_batch` rewrites this for each
    /// function group so the group's shared facts are asserted ONCE and every
    /// bare obligation in the group is decided against them. Empty for the
    /// per-VC `verify` path (no shared prefix), so that path is byte-identical
    /// to before. Cleared on process kill (a restarted process re-sends it via
    /// `send_base_assertions`).
    current_prefix: Vec<CommonAssertion>,
    /// Trust: Names DECLARED by `current_prefix` at the base scope — variable
    /// symbols and, since Lever A's datatype preamble, the `declare-sort` /
    /// `declare-datatype` sort names too. The per-VC push/pop scope SKIPS
    /// re-declaring these (re-declaring a name already bound at an enclosing
    /// scope is an error for most solvers), so the bare obligation references
    /// the base-scope declaration. Empty for the per-VC `verify` path (no
    /// prefix), so that path re-declares exactly as before.
    prefix_declared_vars: std::collections::HashSet<String>,
    /// Trust: The SMT logic to set at the base scope for the current batch.
    ///
    /// `verify_batch` detects this from the union of EVERY full formula in the
    /// function group (prefix ∪ all obligations), so the single base-scope logic
    /// is rich enough for every push/pop query — even when a bare obligation in
    /// isolation would auto-detect a weaker logic than the prefix needs (e.g. a
    /// pure-LIA obligation under a bitvector prefix). `None` for the per-VC path,
    /// which keeps auto-detecting from the first VC's formula exactly as before.
    prefix_logic: Option<String>,
    /// Trust: The session-wide SMT logic pinned by the FIRST `verify_batch`
    /// call, from the first batched VC's FULL formula — exactly the formula the
    /// per-VC dispatch path would have auto-detected its (single, session-long)
    /// `(set-logic …)` from. Batch mode re-initializes the base across function
    /// groups (a prefix change kills the process, see `set_prefix`), so without
    /// a pin each re-init would re-detect a logic from whatever query happens to
    /// come first in the new group — making verdicts depend on group boundaries
    /// where the per-VC path's verdicts do not (observed: a `true` obligation
    /// first in a group pinned `QF_LIA` on the fresh process, degrading the
    /// group's bitvector obligations `sat → unknown` vs the per-VC path).
    /// Pinning replicates the per-VC path's one-logic-per-session behavior, so
    /// batch dispatch stays verdict-identical. `None` until a batch runs; the
    /// pure per-VC path never reads or writes it (its fault-restart re-detect
    /// behavior is unchanged).
    batch_pinned_logic: Option<String>,
}

impl SessionState {
    /// Kill the current solver process.
    fn kill_process(&mut self) {
        // SolverProcess::drop kills its complete group and reaps the leader
        // before its reservation field can release aggregate capacity.
        drop(self.process.take());
        self.base_initialized = false;
    }

    /// Trust: Install a new per-function shared prefix at the base scope.
    ///
    /// Replaces the current prefix wholesale, so the previous function's prefix
    /// is dropped and the new one is sent fresh on the next
    /// `ensure_base_initialized`. Resetting the prefix between functions is a
    /// SOUNDNESS requirement: a stale prefix from function A must never leak
    /// into function B's obligations.
    ///
    /// # Why a prefix CHANGE kills a live process (S2 stage C hardening)
    ///
    /// Base-scope commands are sent at the solver's TOP level — outside any
    /// push/pop — so they can never be retracted from a live process. Merely
    /// flagging `base_initialized = false` (the original behavior) made the
    /// next `send_base_assertions` APPEND the new base onto the old one in the
    /// SAME process: the previous group's prefix stayed asserted (cross-function
    /// fact bleed — with colliding names like `SP` across lifted functions this
    /// is a false-proof channel: a stale contradictory base fact turns a
    /// satisfiable violation formula `unsat` ⇒ wrongly `Proved`), its variable
    /// declarations were re-sent (a redeclaration error for most solvers), and a
    /// SECOND `(set-logic …)` hit the live process (undefined; empirically flips
    /// ay into returning `unknown` for trivially-sat queries). Observed on the
    /// first production engagement of `verify_batch` (targo-trust verify-binary
    /// A/B audit, 2026-07-02). Killing the process guarantees the next query
    /// sees EXACTLY `set-logic ∘ common assertions ∘ current prefix` — nothing
    /// stale — at the cost of one respawn per prefix change (per function
    /// group).
    ///
    /// When the new prefix and logic are IDENTICAL to what is already
    /// installed, this is a no-op: the live process's base scope already
    /// matches, so neither a kill nor a re-init is needed (in particular,
    /// consecutive prefix-less groups keep one persistent process — byte-
    /// identical to the per-VC dispatch path).
    fn set_prefix(&mut self, prefix: Vec<CommonAssertion>, logic: Option<String>) {
        let same_base = self.prefix_logic == logic
            && self.current_prefix.len() == prefix.len()
            && self
                .current_prefix
                .iter()
                .zip(prefix.iter())
                .all(|(cur, new)| cur.commands == new.commands);
        if same_base {
            // Solver-side base already holds exactly this prefix (or no process
            // is live, in which case the next query re-initializes anyway).
            // `prefix_declared_vars` is unchanged (same commands).
            self.current_prefix = prefix;
            self.prefix_logic = logic;
            return;
        }

        // Base content changes: a live process's top-level assertions cannot be
        // retracted, so fail to a fresh process (see doc comment above).
        if self.process.is_some() {
            self.kill_process();
        }

        // Record what the prefix declares — variable symbols AND the datatype/
        // sort names of Lever A's SMT preamble — so the per-VC push scope can
        // skip re-declaring them.
        self.prefix_declared_vars = prefix
            .iter()
            .flat_map(|a| a.commands.iter())
            .filter_map(|cmd| extract_declared_name(cmd))
            .collect();
        self.current_prefix = prefix;
        self.prefix_logic = logic;
        self.base_initialized = false;
    }
}

/// A common assertion that should be shared across all VC scopes.
///
/// These are asserted at the base solver level (outside any push/pop scope)
/// so they persist across all VC queries. Typical examples include type
/// constraints, range bounds, and shared variable declarations.
#[derive(Debug, Clone)]
pub struct CommonAssertion {
    /// Human-readable label for this assertion group.
    pub label: String,
    /// SMT-LIB2 commands (declarations + assertions) for this group.
    pub commands: Vec<String>,
}

impl CommonAssertion {
    /// Create a common assertion from a trust-types Formula.
    ///
    /// Generates the necessary variable declarations and assertion commands.
    #[must_use]
    pub fn from_formula(label: impl Into<String>, formula: &Formula) -> Self {
        let mut commands = Vec::new();

        // Emit variable declarations.
        for decl in smt2_export::emit_declarations(formula) {
            commands.push(decl);
        }

        // Emit the assertion.
        commands.push(format!("(assert {})", smt2_export::formula_to_smt2(formula)));

        CommonAssertion { label: label.into(), commands }
    }

    /// Create a common assertion from raw SMT-LIB2 commands.
    #[must_use]
    pub fn from_commands(label: impl Into<String>, commands: Vec<String>) -> Self {
        CommonAssertion { label: label.into(), commands }
    }
}

/// Incremental AY session that maintains a persistent solver
/// context with push/pop scoping.
///
/// # Architecture
///
/// ```text
/// Base Level (persistent):
///   - Logic declaration
///   - Common variable declarations
///   - Common assertions (type constraints, invariants)
///   - Learned lemmas (persisted by solver across push/pop)
///
/// Per-VC Scope (push/pop):
///   (push 1)
///     - VC-specific declarations
///     - VC formula assertion
///     - (check-sat) + result extraction
///   (pop 1)
/// ```
///
/// # Fault Isolation
///
/// On solver crash or timeout:
/// 1. The solver process is killed and restarted.
/// 2. Common assertions are re-asserted on the new process.
/// 3. After `MAX_CONSECUTIVE_FAILURES`, permanently falls back to per-process mode.
pub struct IncrementalAYSession {
    /// Path to the solver binary.
    solver_path: String,
    /// Extra arguments passed to the solver.
    solver_args: Vec<String>,
    /// Timeout per query in milliseconds.
    query_timeout_ms: u64,
    /// Per-job memory ceiling in MB (the `solver_memory_limit_mb` config). When
    /// set, it is (a) propagated into the spawned `ay` as `--memory <mb>` so the
    /// solver self-limits and returns Unknown on pressure instead of OOMing, and
    /// (b) the size of the aggregate reservation taken from the cross-process
    /// `memory_jobserver` before each spawn. `None` is possible only when no
    /// host ceiling can be derived; a configured authority then fails before
    /// spawn rather than authorizing an unbounded solver.
    solver_memory_limit_mb: Option<u64>,
    /// Common assertions shared across all VCs.
    common_assertions: Vec<CommonAssertion>,
    /// SMT-LIB2 logic string (e.g., "QF_LIA", "QF_BV").
    logic: Option<String>,
    /// Mutable session state behind a Mutex for `Sync` compliance.
    /// Required because `VerificationBackend` trait demands `Send + Sync`.
    state: Mutex<SessionState>,
}

/// One immutable coupling between the exact `--memory` argument and aggregate
/// admission bytes for a single solver spawn. Environment/configuration is read
/// once when this plan is built; neither side may independently re-read it.
struct SolverMemoryPlan {
    limit_mb: Option<u64>,
    reservation_bytes: u64,
    args: Vec<String>,
}

impl IncrementalAYSession {
    /// Create a new incremental session with the default ay solver.
    #[must_use]
    pub fn new() -> Self {
        Self::with_solver_path("ay")
    }

    /// Create a new incremental session with a custom solver path.
    #[must_use]
    pub fn with_solver_path(path: impl Into<String>) -> Self {
        IncrementalAYSession {
            solver_path: path.into(),
            // Trust: `-in` and `--incremental` are the SAME ay flag (the z3-compat
            // `-in` alias resolves to `--incremental`); passing both makes ay
            // reject the invocation ("--incremental cannot be used multiple
            // times") so it prints only its session banner and every solve
            // degrades to Unknown. `--incremental` alone reads stdin line-by-line,
            // which is exactly the incremental push/pop protocol here.
            solver_args: vec![
                "--z3-mode".to_string(),
                "-smt2".to_string(),
                "--incremental".to_string(),
            ],
            query_timeout_ms: DEFAULT_QUERY_TIMEOUT_MS,
            solver_memory_limit_mb: None,
            common_assertions: Vec::new(),
            logic: None,
            state: Mutex::new(SessionState {
                process: None,
                base_initialized: false,
                consecutive_failures: 0,
                fallen_back: false,
                stats: IncrementalAYStats::default(),
                current_prefix: Vec::new(),
                prefix_declared_vars: std::collections::HashSet::new(),
                prefix_logic: None,
                batch_pinned_logic: None,
            }),
        }
    }

    /// Set the per-query timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.query_timeout_ms = timeout_ms;
        self
    }

    /// Set the per-job memory ceiling in MB (the `solver_memory_limit_mb`
    /// config). This is propagated to the spawned `ay` as `--memory <mb>` so the
    /// solver returns Unknown under memory pressure instead of OOM-killing the
    /// host, and is the size of the aggregate reservation taken from the
    /// cross-process `memory_jobserver` before each spawn. A value of `0` clears
    /// only this explicit override; environment or derived ceilings still apply.
    #[must_use]
    pub fn with_memory_limit_mb(mut self, limit_mb: u64) -> Self {
        self.solver_memory_limit_mb = if limit_mb == 0 { None } else { Some(limit_mb) };
        self
    }

    /// The per-job memory ceiling actually in force. Precedence:
    ///
    /// 1. the explicit `solver_memory_limit_mb` when set (targo's binary router);
    /// 2. nonzero `TRUST_SOLVER_MEMORY_LIMIT_MB` from the environment (`0`
    ///    clears the override and falls through to the derived ceiling, matching
    ///    `with_memory_limit_mb(0)`) — previously honored only outside the
    ///    compiler, by targo's router, never by this in-compiler session, so the
    ///    documented knob silently did nothing on the plain `cargo` lane;
    /// 3. the budget-derived per-job ceiling (70 % of RAM / parallelism,
    ///    1 GiB floor) — no longer gated on the memory-jobserver being active:
    ///    plain `cargo`→`trustc` never has the jobserver env, which left every
    ///    spawned `ay` fully unbounded on the DEFAULT lane while the strict
    ///    `targo trust` lane (which does export it) was the guarded one. A
    ///    spawned solver should never be unbounded by default; `--memory` only
    ///    degrades a too-hungry solve to Unknown, it cannot change a verdict.
    ///
    /// `None` only when RAM is undetectable (the historical unbounded
    /// behavior, now the exception rather than the default).
    fn effective_memory_limit_mb(&self) -> Option<u64> {
        if self.solver_memory_limit_mb.is_some() {
            return self.solver_memory_limit_mb;
        }
        if let Ok(raw) = std::env::var("TRUST_SOLVER_MEMORY_LIMIT_MB") {
            if let Ok(mb) = raw.trim().parse::<u64>() {
                if mb != 0 {
                    return Some(mb);
                }
            }
        }
        crate::memory_jobserver::default_per_job_limit_mb()
    }

    /// The args to pass to a spawned `ay`, with the per-job `--memory <mb>`
    /// ceiling appended when configured. Centralizes the propagation so both the
    /// incremental and per-process spawn paths stay consistent.
    fn solver_memory_plan(&self) -> Result<SolverMemoryPlan, String> {
        if self.solver_args.iter().any(|argument| argument == "--memory") {
            return Err(format!(
                "{PRE_SPAWN_ADMISSION_PREFIX} solver_args contains an unmanaged --memory flag; use with_memory_limit_mb so enforced capacity and aggregate admission remain identical"
            ));
        }
        let limit_mb = self.effective_memory_limit_mb();
        let mut args = self.solver_args.clone();
        let reservation_bytes = if let Some(mb) = limit_mb {
            // `ay --memory <MB>` self-limits and degrades to Unknown on pressure.
            args.push("--memory".to_string());
            args.push(mb.to_string());
            mb.checked_mul(1024 * 1024).ok_or_else(|| {
                format!(
                    "{PRE_SPAWN_ADMISSION_PREFIX} --memory {mb} MiB is not representable as an exact reservation"
                )
            })?
        } else {
            crate::coordinator::default_reservation_bytes()
                .map_err(|error| format!("{PRE_SPAWN_ADMISSION_PREFIX} {error}"))?
        };
        Ok(SolverMemoryPlan { limit_mb, reservation_bytes, args })
    }

    /// Acquire an aggregate-memory reservation sized to the per-job ceiling from
    /// the cross-process budget, BEFORE spawning `ay`. Inert (no-op) only when no
    /// coordinator is configured or discovered. An active authority with no
    /// derivable ceiling, or any configured-domain failure, returns an error and
    /// must stop before process creation.
    ///
    // Trust: routes through `coordinator::reserve`, which prefers the trustd
    // daemon (rung 2) or selects the file ledger only when no daemon lane was
    // provisioned. Once selected, failure is explicit and never launches an
    // unreserved solver or crosses into another authority.
    fn acquire_reservation(
        &self,
        plan: &SolverMemoryPlan,
    ) -> Result<crate::coordinator::Reservation, String> {
        if let Some(limit_mb) = plan.limit_mb {
            debug_assert_eq!(
                limit_mb.checked_mul(1024 * 1024),
                Some(plan.reservation_bytes),
                "the immutable spawn plan couples --memory to admission bytes"
            );
        }
        crate::coordinator::reserve(plan.reservation_bytes)
            .map_err(|error| format!("{PRE_SPAWN_ADMISSION_PREFIX} {error}"))
    }

    /// Set the SMT-LIB2 logic for this session.
    ///
    /// If not set, the logic is auto-detected from the first VC's formula.
    #[must_use]
    pub fn with_logic(mut self, logic: impl Into<String>) -> Self {
        self.logic = Some(logic.into());
        self
    }

    /// Add a common assertion that will be shared across all VCs.
    ///
    /// Common assertions are sent once at the base solver level and persist
    /// across push/pop scopes. Use for type constraints, range bounds, and
    /// other assertions that apply to all VCs in a batch.
    pub fn add_common_assertion(&mut self, assertion: CommonAssertion) {
        self.common_assertions.push(assertion);
        let count = self.common_assertions.len();
        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.common_assertions = count;
        // Force re-initialization on next query so the new assertion is sent.
        st.base_initialized = false;
    }

    /// Add common assertions from a set of formulas.
    ///
    /// Each formula becomes a separate common assertion group.
    pub fn add_common_formulas(&mut self, formulas: &[(String, Formula)]) {
        for (label, formula) in formulas {
            self.add_common_assertion(CommonAssertion::from_formula(label, formula));
        }
    }

    /// Return a snapshot of the session statistics.
    #[must_use]
    pub fn stats(&self) -> IncrementalAYStats {
        let st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.clone()
    }

    /// Verify a single VC using the incremental session.
    ///
    /// Uses push/pop to isolate the VC's assertions while sharing
    /// common assertions from the base level.
    pub fn verify_vc(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "ay-incremental", 0)
        {
            // Unsupported-MIR VCs may carry an incomplete (unsound-to-relax)
            // encoding, so they are NOT eligible for the nonlinear relaxation.
            return result;
        }
        if let Some(result) = mul_counterexample(vc) {
            return result;
        }

        let result = self.verify_vc_solved(vc);
        self.relax_if_unknown(vc, result)
    }

    /// The core solve for a VC (incremental session, with per-process fallback).
    fn verify_vc_solved(&self, vc: &VerificationCondition) -> VerificationResult {
        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.total_queries += 1;

        // Permanently fallen back: use per-process mode.
        if st.fallen_back {
            st.stats.fallback_queries += 1;
            drop(st); // Release lock before per-process call.
            return self.verify_per_process(vc);
        }

        match self.verify_incremental(&mut st, vc) {
            Ok(result) => {
                st.consecutive_failures = 0;
                st.stats.incremental_queries += 1;
                result
            }
            Err(err) => {
                if is_pre_spawn_admission_error(&err) {
                    return VerificationResult::Unknown {
                        solver: "ay-incremental".into(),
                        time_ms: 0,
                        reason: err,
                    };
                }
                let is_timeout = err.contains("timeout");
                st.kill_process();
                st.consecutive_failures += 1;
                st.stats.restarts += 1;

                if st.consecutive_failures >= MAX_CONSECUTIVE_FAILURES {
                    st.fallen_back = true;
                    st.stats.permanently_fallen_back = true;
                }

                if is_timeout {
                    return VerificationResult::Timeout {
                        solver: "ay-incremental".into(),
                        timeout_ms: self.query_timeout_ms,
                    };
                }

                st.stats.fallback_queries += 1;
                drop(st); // Release lock before per-process call.
                self.verify_per_process(vc)
            }
        }
    }

    /// On an `Unknown` verdict, retry once against a SOUND RELAXATION of the VC:
    /// every nonlinear atom (`Rem`/`Div` by a non-constant, `Mul` of two
    /// non-constants, and the bitvector analogues) is replaced by a fresh,
    /// unconstrained variable. The relaxation has a SUPERSET of the original's
    /// models (each original model extends to one of the relaxation by giving the
    /// fresh vars the abstracted terms' values), so `relaxation UNSAT ⟹ original
    /// UNSAT ⟹ obligation holds`. This recovers obligations whose proof needs only
    /// the LINEAR core but whose nonlinear terms drive ay to `unknown`
    /// (QF_NIA incompleteness) — e.g. `s[n % s.len()]`, whose bound
    /// `s.len() != 0 ⟹ n % s.len() < s.len()` is linear once the `mod` is dropped.
    ///
    /// Purely additive: only fires on `Unknown`, and only ever UPGRADES it to
    /// `Proved` (when the relaxation is UNSAT) — a `sat`/`unknown`/timeout
    /// relaxation leaves the original `Unknown` untouched. So it can never change a
    /// `Proved` or `Failed` verdict, and is sound regardless of the abstraction's
    /// precision.
    fn relax_if_unknown(
        &self,
        vc: &VerificationCondition,
        result: VerificationResult,
    ) -> VerificationResult {
        if !matches!(result, VerificationResult::Unknown { .. }) {
            return result;
        }
        // A nonlinear relaxation still needs the same unavailable admission
        // authority. Do not turn one fail-closed infrastructure result into a
        // second admission wait merely because the VC contains nonlinear terms.
        if matches!(
            &result,
            VerificationResult::Unknown { reason, .. }
                if is_pre_spawn_admission_error(reason)
        ) {
            return result;
        }
        let Some(relaxed_formula) = abstract_nonlinear(&vc.formula) else {
            return result;
        };
        let relaxed_vc = VerificationCondition { formula: relaxed_formula, ..vc.clone() };
        // Trust (B5): solve the relaxed VC through the LIVE push/pop session
        // (reusing the base context + learned lemmas) instead of spawning a fresh
        // `ay` subprocess. Falls back to the subprocess when the session is
        // unavailable after a solver/session fault. Pre-spawn admission failures
        // return once without retry. The relaxed verdict is read exactly as
        // before: only an `unsat` (⟹ `Proved`) upgrades the original `Unknown`;
        // anything else keeps it.
        match self.solve_relaxed(&relaxed_vc) {
            VerificationResult::Proved { time_ms, strength, solver_warnings, .. } => {
                VerificationResult::Proved {
                    solver: "ay-nonlinear-relaxation".into(),
                    time_ms,
                    strength,
                    proof_certificate: None,
                    solver_warnings,
                    native_proof_envelope: None,
                }
            }
            // relaxation sat / unknown / timeout: no sound conclusion — keep Unknown.
            _ => result,
        }
    }

    /// Trust (B5): solve a (relaxed) VC through the LIVE incremental session,
    /// reusing the persistent push/pop context and learned lemmas, with the same
    /// per-process fallback semantics as [`Self::verify_vc_solved`].
    ///
    /// Behaviorally equivalent to `self.verify_per_process(vc)` for the purpose
    /// of [`Self::relax_if_unknown`]: it returns a `Proved` exactly when the
    /// solver finds the VC `unsat`. The push/pop balance is maintained by
    /// [`Self::verify_incremental`] (every branch pops its scope before
    /// returning `Ok`; on `Err` the process is killed and rebuilt fresh), so a
    /// relaxed query can never corrupt the base context of subsequent VCs.
    ///
    /// Falls back to a fresh `ay` subprocess after a solver/session error or
    /// timeout (the process is killed, the failure counters advance exactly as
    /// on the primary path, and the relaxed query is retried out-of-process).
    /// Pre-spawn admission/configuration errors are infrastructure results, not
    /// solver faults: they return once without retry or poisoning the session.
    fn solve_relaxed(&self, relaxed_vc: &VerificationCondition) -> VerificationResult {
        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.total_queries += 1;

        // Permanently fallen back: session unavailable, use per-process mode.
        if st.fallen_back {
            st.stats.fallback_queries += 1;
            drop(st); // Release lock before per-process call.
            return self.verify_per_process(relaxed_vc);
        }

        match self.verify_incremental(&mut st, relaxed_vc) {
            Ok(result) => {
                st.consecutive_failures = 0;
                st.stats.incremental_queries += 1;
                result
            }
            Err(err) => {
                if is_pre_spawn_admission_error(&err) {
                    return VerificationResult::Unknown {
                        solver: "ay-incremental".into(),
                        time_ms: 0,
                        reason: err,
                    };
                }
                // Session fault: kill + rebuild on next query, advance the same
                // failure counters as the primary path, then solve the relaxed
                // VC out-of-process so the verdict is still sound.
                st.kill_process();
                st.consecutive_failures += 1;
                st.stats.restarts += 1;

                if st.consecutive_failures >= MAX_CONSECUTIVE_FAILURES {
                    st.fallen_back = true;
                    st.stats.permanently_fallen_back = true;
                }

                st.stats.fallback_queries += 1;
                drop(st); // Release lock before per-process call.
                self.verify_per_process(relaxed_vc)
            }
        }
    }

    /// Verify a batch of VCs, sharing each function's common assertion prefix
    /// across all of that function's obligations.
    ///
    /// This is the primary entry point for batch incremental verification.
    /// Returns `(vc, result)` pairs in the SAME ORDER as the input, one per
    /// input VC, with each returned `vc` being the ORIGINAL pre-conjoined VC (so
    /// any downstream cache that keys on `vc.formula` sees the full
    /// `prefix ∧ obligation` conjunction, unchanged by the split).
    ///
    /// # Algorithm
    ///
    /// VCs are grouped by `vc.function` (preserving first-seen order). For each
    /// group, `split_shared_prefix` computes the conjuncts present in EVERY VC
    /// of the group; that prefix is installed ONCE at the solver's base scope
    /// (via `SessionState::set_prefix`), and each obligation is decided as a
    /// small per-VC delta in its own push/pop scope. The solver therefore
    /// decides `prefix ∧ bare_obligation` for each VC — exactly the original
    /// pre-conjoined formula as a logical value (`And` is commutative,
    /// associative, and idempotent), so the verdict is identical to the per-VC
    /// path. The win is `M·N → M+N` assert work for a function with M
    /// obligations over an N-conjunct prefix.
    ///
    /// # Soundness
    ///
    /// - The prefix is RESET between function groups (and cleared at the end), so
    ///   one function's facts can never leak into another's obligations.
    /// - On any session fault (or permanent fallback), the FULL pre-conjoined
    ///   formula — not the bare obligation — is solved out-of-process, so a
    ///   transient session error can never drop the prefix and false-prove an
    ///   obligation.
    /// - The unsupported-MIR / forced-multiplication / nonlinear-relaxation
    ///   guards run on the FULL formula, identically to the per-VC path.
    #[must_use]
    pub fn verify_batch(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        if vcs.is_empty() {
            return Vec::new();
        }

        // Trust: pin the session logic ONCE, from the first batched VC's FULL
        // formula — exactly the formula the per-VC path's single session-long
        // base init would have auto-detected `(set-logic …)` from. Batch mode
        // re-initializes the base whenever a group's prefix changes (a fresh
        // process, see `set_prefix`), and without the pin each re-init would
        // re-detect a logic from whatever query the new group happens to start
        // with — making verdicts depend on group boundaries where the per-VC
        // path's do not. See `SessionState::batch_pinned_logic`.
        {
            let mut st = self.state.lock().expect("invariant: mutex not poisoned");
            if st.batch_pinned_logic.is_none() {
                st.batch_pinned_logic =
                    Some(smt2_export::detect_logic(&vcs[0].formula).to_string());
            }
        }

        // Group VC indices by function, preserving first-seen order.
        let mut group_order: Vec<Symbol> = Vec::new();
        let mut groups: std::collections::HashMap<Symbol, Vec<usize>> =
            std::collections::HashMap::new();
        for (i, vc) in vcs.iter().enumerate() {
            groups.entry(vc.function).or_insert_with(|| {
                group_order.push(vc.function);
                Vec::new()
            });
            groups.get_mut(&vc.function).expect("just inserted").push(i);
        }

        // Results placed back by original index so output order == input order.
        let mut results: Vec<Option<VerificationResult>> = (0..vcs.len()).map(|_| None).collect();

        for function in &group_order {
            let indices = &groups[function];

            // Partition this function's VCs into:
            //  - NONLINEAR: full formula has a relaxable nonlinear atom, so the
            //    per-VC path may upgrade Unknown→Proved via the live-session
            //    relaxation. These are solved with an EMPTY base scope, exactly
            //    reproducing the non-batch `verify_vc` (live session over empty
            //    base, relaxation over empty base) — so their verdict is
            //    byte-identical and the shared prefix can never alter it.
            //  - LINEAR: no relaxable nonlinear atom ⇒ relaxation never fires ⇒
            //    deciding `prefix ∧ bare` against the base scope is exactly
            //    `prefix ∧ obligation`. Only these are batched.
            let mut linear: Vec<usize> = Vec::new();
            let mut nonlinear: Vec<usize> = Vec::new();
            for &i in indices {
                if abstract_nonlinear(&vcs[i].formula).is_some() {
                    nonlinear.push(i);
                } else {
                    linear.push(i);
                }
            }

            // Solve the nonlinear VCs over an EMPTY base scope first (clears any
            // prefix a previous group installed), verbatim per-VC path.
            if !nonlinear.is_empty() {
                self.install_prefix(&[], &[]);
                for &i in &nonlinear {
                    results[i] = Some(self.verify_vc(&vcs[i]));
                }
            }

            if linear.is_empty() {
                continue;
            }

            // Trust: a SINGLETON group has nothing to share — hoisting its one
            // formula to the base scope is zero throughput win (one base assert
            // + one trivial `true` check vs. one push-scope assert) yet changes
            // the query PRESENTATION, which can perturb the solver's model
            // choice for a refuted obligation vs. the per-VC path. Solve it on
            // the verbatim per-VC path (clearing any prefix a previous group
            // installed), byte-identical to non-batch dispatch.
            if linear.len() == 1 {
                let i = linear[0];
                self.install_prefix(&[], &[]);
                results[i] = Some(self.verify_vc(&vcs[i]));
                continue;
            }

            let linear_vcs: Vec<VerificationCondition> =
                linear.iter().map(|&i| vcs[i].clone()).collect();

            // Split out the conjuncts shared by every LINEAR VC in this group.
            let (prefix_formulas, bare_vcs) = split_shared_prefix(&linear_vcs);

            if prefix_formulas.is_empty() {
                // No shared prefix ⇒ nothing to hoist; verify each full VC on the
                // per-VC path (byte-identical to non-batch dispatch). Clear any
                // base scope from a PREVIOUS group first.
                self.install_prefix(&[], &linear_vcs);
                for (&i, full_vc) in linear.iter().zip(linear_vcs.iter()) {
                    results[i] = Some(self.verify_vc(full_vc));
                }
                continue;
            }

            // Install this group's prefix at the base scope (once), with a logic
            // wide enough for every full formula in the group.
            self.install_prefix(&prefix_formulas, &linear_vcs);

            for ((&i, full_vc), bare_vc) in
                linear.iter().zip(linear_vcs.iter()).zip(bare_vcs.iter())
            {
                results[i] = Some(self.verify_bare_against_prefix(bare_vc, full_vc));
            }
        }

        // Clear the base scope so a later plain `verify` call is not decided
        // against a stale prefix.
        self.install_prefix(&[], &[]);

        vcs.iter()
            .zip(results)
            .map(|(vc, r)| {
                (
                    vc.clone(),
                    r.unwrap_or_else(|| VerificationResult::Unknown {
                        solver: "ay-incremental".into(),
                        time_ms: 0,
                        reason: "batch slot unfilled".to_string(),
                    }),
                )
            })
            .collect()
    }

    /// Install `prefix_formulas` as the base-scope shared assertion prefix, with
    /// an SMT logic wide enough for every VC in `group_vcs` (prefix ∪
    /// obligations). Passing an empty `prefix_formulas` clears any base scope a
    /// previous group installed.
    fn install_prefix(&self, prefix_formulas: &[Formula], group_vcs: &[VerificationCondition]) {
        let prefix: Vec<CommonAssertion> = prefix_formulas
            .iter()
            .enumerate()
            .map(|(i, f)| CommonAssertion::from_formula(format!("shared-prefix-{i}"), f))
            .collect();

        // Detect a logic that covers EVERY full formula in the group (the prefix
        // conjuncts are a subset of each, so analyzing the obligations suffices),
        // so the single base-scope `(set-logic ...)` is never too weak for a
        // member query. `None` ⇒ keep per-VC auto-detect (empty prefix).
        let logic = if prefix.is_empty() { None } else { Some(detect_group_logic(group_vcs)) };

        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.set_prefix(prefix, logic);
    }

    /// Decide `bare_vc` against the currently-installed base-scope prefix,
    /// returning a verdict identical to verifying `full_vc` (= prefix ∧ bare) on
    /// the per-VC path.
    ///
    /// The unsupported-MIR / forced-multiplication / relaxation guards run on the
    /// FULL formula (matching `verify_vc`). The core solve runs on the bare
    /// delta against the base scope; ANY session unavailability solves the FULL
    /// formula out-of-process, so the prefix is never silently dropped.
    fn verify_bare_against_prefix(
        &self,
        bare_vc: &VerificationCondition,
        full_vc: &VerificationCondition,
    ) -> VerificationResult {
        if let Some(result) =
            crate::backend_trait::unsupported_mir_unknown(full_vc, "ay-incremental", 0)
        {
            return result;
        }
        if let Some(result) = mul_counterexample(full_vc) {
            return result;
        }

        // INVARIANT: `verify_batch` only routes a VC here when its FULL formula
        // has NO relaxable nonlinear atom (`abstract_nonlinear` ⇒ None). The
        // per-VC path's only Unknown→Proved upgrade is the nonlinear relaxation,
        // which therefore cannot fire for this VC — so deciding the bare
        // obligation against the base-scope prefix yields exactly the per-VC
        // verdict for `prefix ∧ obligation`, with no relaxation divergence.
        debug_assert!(
            abstract_nonlinear(&full_vc.formula).is_none(),
            "verify_bare_against_prefix must only receive relaxation-free VCs"
        );
        self.solve_bare_against_prefix(bare_vc, full_vc)
    }

    /// Core bare-delta solve against the installed base scope, with the per-VC
    /// fallback semantics of [`Self::verify_vc_solved`] — except the fallback
    /// solves the FULL formula so the prefix is preserved.
    fn solve_bare_against_prefix(
        &self,
        bare_vc: &VerificationCondition,
        full_vc: &VerificationCondition,
    ) -> VerificationResult {
        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.total_queries += 1;

        // Permanently fallen back: the base scope is unavailable, so solve the
        // FULL formula per-process (it carries the prefix).
        if st.fallen_back {
            st.stats.fallback_queries += 1;
            drop(st);
            return self.verify_per_process(full_vc);
        }

        match self.verify_incremental(&mut st, bare_vc) {
            Ok(result) => {
                st.consecutive_failures = 0;
                st.stats.incremental_queries += 1;
                result
            }
            Err(err) => {
                if is_pre_spawn_admission_error(&err) {
                    return VerificationResult::Unknown {
                        solver: "ay-incremental".into(),
                        time_ms: 0,
                        reason: err,
                    };
                }
                let is_timeout = err.contains("timeout");
                st.kill_process();
                st.consecutive_failures += 1;
                st.stats.restarts += 1;

                if st.consecutive_failures >= MAX_CONSECUTIVE_FAILURES {
                    st.fallen_back = true;
                    st.stats.permanently_fallen_back = true;
                }

                if is_timeout {
                    return VerificationResult::Timeout {
                        solver: "ay-incremental".into(),
                        timeout_ms: self.query_timeout_ms,
                    };
                }

                st.stats.fallback_queries += 1;
                drop(st); // Release lock before per-process call.
                // FULL formula (carries the prefix): never drop a shared fact on
                // a session fault.
                self.verify_per_process(full_vc)
            }
        }
    }

    /// Extract common type constraints from a set of VCs.
    ///
    /// Analyzes the VCs to find declarations that appear across multiple VCs and
    /// promotes them to shared declarations. This avoids re-declaring common
    /// symbols in each push/pop scope.
    ///
    /// Trust: a declaration is any command with a declaration identity —
    /// `declare-fun` / `declare-const` variables AND the `declare-sort` /
    /// `declare-datatype` commands of Lever A's SMT preamble. Dropping the
    /// latter would promote a `(declare-fun e () Expr)` whose sort `Expr` was
    /// never declared, making the base scope itself malformed.
    pub fn extract_common_declarations(&mut self, vcs: &[VerificationCondition]) {
        use std::collections::BTreeMap;

        // Count declaration occurrences across VCs, keyed by declared name.
        let mut decl_counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut decl_text: BTreeMap<String, String> = BTreeMap::new();
        // Sort/datatype names in FIRST-SEEN order. `emit_declarations` emits
        // sorts before the `declare-fun`s that use them and topologically orders
        // datatypes among themselves; promoting by name order alone would break
        // that (`(declare-fun X () expr)` sorts before `(declare-datatype expr
        // …)`), so the sort declarations are replayed in emission order ahead of
        // the order-insensitive value declarations.
        let mut sort_order: Vec<String> = Vec::new();

        for vc in vcs {
            let decls = smt2_export::emit_declarations(&vc.formula);
            for decl in &decls {
                // Declaration identity of e.g. "(declare-fun x () Int)" or
                // "(declare-datatype Expr ((Leaf) (Node (l Expr) (r Expr))))".
                if let Some(name) = extract_declared_name(decl) {
                    *decl_counts.entry(name.clone()).or_insert(0) += 1;
                    if declares_sort(decl) && !sort_order.contains(&name) {
                        sort_order.push(name.clone());
                    }
                    decl_text.entry(name).or_insert_with(|| decl.clone());
                }
            }
        }

        // Promote declarations that appear in 2+ VCs, sorts first (in emission
        // order), then the value declarations in name order as before.
        let mut shared_decls: Vec<String> = Vec::new();
        for name in &sort_order {
            if decl_counts.get(name).is_some_and(|count| *count >= 2) {
                shared_decls.extend(decl_text.get(name).cloned());
            }
        }
        for (name, count) in &decl_counts {
            if *count >= 2 && !sort_order.contains(name) {
                shared_decls.extend(decl_text.get(name).cloned());
            }
        }

        if !shared_decls.is_empty() {
            self.add_common_assertion(CommonAssertion::from_commands(
                "shared-variable-declarations",
                shared_decls,
            ));
        }
    }

    // -- Internal methods --

    /// Run a single VC on the persistent solver using push/pop.
    fn verify_incremental(
        &self,
        st: &mut SessionState,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, String> {
        let timeout = Duration::from_millis(self.query_timeout_ms);
        let start = Instant::now();
        let deadline = start.checked_add(timeout).unwrap_or(start);
        self.ensure_base_initialized(st, vc, deadline)?;

        // Snapshot what the base-scope prefix already declares (variables AND
        // datatype/sort names), so the per-VC push scope below does NOT
        // re-declare them. Cloning the (usually small, often empty) set
        // sidesteps borrowing `st` while `st.process` is borrowed mutably as
        // `proc`. Empty for the per-VC path ⇒ no skips ⇒ byte-identical to
        // before.
        let base_declared: std::collections::HashSet<String> = st.prefix_declared_vars.clone();
        // Compute the scope's declarations BEFORE taking the &mut borrow on
        // `st.process`.
        let vc_declarations = scope_declarations(&vc.formula, &base_declared);

        let proc = st.process.as_mut().ok_or("no solver process")?;
        // Push a new scope for this VC.
        send_command_until(proc, "(push 1)", deadline)?;

        // Declare VC-specific symbols and sorts (those already declared at base
        // level were dropped by `scope_declarations`).
        for decl in &vc_declarations {
            send_command_until(proc, decl, deadline)?;
        }

        // Assert the VC formula.
        let assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));
        send_command_until(proc, &assertion, deadline)?;

        // Check satisfiability.
        send_command_until(proc, "(check-sat)", deadline)?;
        let sat_line = read_response_line(proc, remaining_timeout(timeout, start))?;

        let elapsed = start.elapsed().as_millis() as u64;

        // Parse result.
        let result = if sat_line.trim() == "unsat" {
            return Ok(finish_bare_unsat(st, elapsed, deadline));
        } else if sat_line.trim() == "sat" {
            // Get model for counterexample.
            send_command_until(proc, "(get-model)", deadline)?;
            let model_output = read_model_response(proc, remaining_timeout(timeout, start))?;

            send_command_until(proc, "(pop 1)", deadline)?;

            let full_output = format!("sat\n{model_output}");
            smtlib_backend::parse_solver_output(&full_output, elapsed, vec![])
        } else if sat_line.trim() == "unknown" {
            send_command_until(proc, "(pop 1)", deadline)?;
            VerificationResult::Unknown {
                solver: "ay-incremental".into(),
                time_ms: elapsed,
                reason: "solver returned unknown".to_string(),
            }
        } else {
            let _ = send_command_until(proc, "(pop 1)", deadline);
            return Err(format!("unexpected solver response: {}", sat_line.trim()));
        };

        Ok(result)
    }

    /// Ensure the solver process is running and base-level assertions are sent.
    fn ensure_base_initialized(
        &self,
        st: &mut SessionState,
        vc: &VerificationCondition,
        deadline: Instant,
    ) -> Result<(), String> {
        if st.process.is_none() {
            let proc = self.spawn_solver_until(deadline)?;
            st.process = Some(proc);
            st.base_initialized = false;
        }

        if !st.base_initialized {
            self.send_base_assertions(st, vc, deadline)?;
            st.base_initialized = true;
        }

        Ok(())
    }

    /// Send base-level setup: logic, common declarations, common assertions.
    ///
    /// Trust: the base scope holds, in order, (1) the static `common_assertions`
    /// configured on the session and (2) the per-function shared prefix
    /// `st.current_prefix` installed by `verify_batch`. Both are asserted ONCE
    /// here and persist across the per-VC push/pop scopes. When `current_prefix`
    /// is empty (the per-VC `verify` path), this is byte-identical to the prior
    /// behavior.
    fn send_base_assertions(
        &self,
        st: &mut SessionState,
        vc: &VerificationCondition,
        deadline: Instant,
    ) -> Result<(), String> {
        // Snapshot the per-function prefix commands + batch logic BEFORE taking
        // the &mut borrow on `st.process` (cannot hold both an immutable borrow
        // of `st.current_prefix` and a mutable borrow of `st.process`).
        let prefix_commands: Vec<String> =
            st.current_prefix.iter().flat_map(|a| a.commands.iter().cloned()).collect();
        let batch_logic = st.prefix_logic.clone();
        let pinned_logic = st.batch_pinned_logic.clone();

        let proc = st.process.as_mut().ok_or("no solver process")?;

        // Set logic. Precedence: explicit session logic > batch-pinned session
        // logic (set once by the first `verify_batch` call from its first VC's
        // FULL formula, so every base re-init across function groups uses the
        // SAME logic the per-VC path would have pinned for the whole session) >
        // per-group batch logic (covers the group: prefix ∪ obligations) >
        // auto-detect from the (possibly bare) representative VC.
        let logic = self
            .logic
            .clone()
            .or(pinned_logic)
            .or(batch_logic)
            .unwrap_or_else(|| smt2_export::detect_logic(&vc.formula).to_string());
        send_command_until(proc, &format!("(set-logic {logic})"), deadline)?;
        // ay does not respond to set-logic.

        // Send all static common assertion groups.
        for assertion in &self.common_assertions {
            for cmd in &assertion.commands {
                send_command_until(proc, cmd, deadline)?;
                // ay does not respond to declarations or assertions.
            }
        }

        // Send the per-function shared prefix (declarations + assertions),
        // asserted once at the base scope so every per-VC push/pop scope in the
        // current function's batch reuses it.
        for cmd in &prefix_commands {
            send_command_until(proc, cmd, deadline)?;
        }

        Ok(())
    }

    /// Spawn a fresh solver process with incremental-mode options.
    fn spawn_solver(&self) -> Result<SolverProcess, String> {
        let start = Instant::now();
        let deadline =
            start.checked_add(Duration::from_millis(self.query_timeout_ms)).unwrap_or(start);
        self.spawn_solver_until(deadline)
    }

    fn spawn_solver_until(&self, deadline: Instant) -> Result<SolverProcess, String> {
        // Reserve the per-job memory budget from the cross-process token bucket
        // BEFORE spawning, so N concurrent workers cannot collectively exceed the
        // machine budget. The reservation rides on the SolverProcess and is freed
        // when the process is dropped/killed. It is inert only when no authority
        // is configured; a selected authority that cannot derive a ceiling fails.
        let memory_plan = self.solver_memory_plan()?;
        let mut reservation = self.acquire_reservation(&memory_plan)?;
        let mut command = Command::new(&self.solver_path);
        command
            .args(&memory_plan.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            // Persistent stderr was never consumed; a pipe could fill and
            // deadlock the solver. The incremental protocol uses stdout only.
            .stderr(Stdio::null());
        isolate_solver_process_group(&mut command);
        reservation
            .configure_child_lifetime_guard(&mut command)
            .map_err(|error| format!("{PRE_SPAWN_LIFETIME_PREFIX} {error}"))?;
        let mut child =
            command.spawn().map_err(|e| format!("failed to spawn {}: {e}", self.solver_path))?;
        // The pre-exec lifetime guard owns a parent-side staging duplicate.
        // `Command::spawn` retains pre-exec closures, so release that duplicate
        // now; the Reservation and spawned child remain the only live owners.
        drop(command);

        let stdin = match child.stdin.take() {
            Some(stdin) => stdin,
            None => {
                terminate_solver_process_group(&mut child, true);
                return Err("failed to capture solver stdin".to_string());
            }
        };
        let stdout = match child.stdout.take() {
            Some(stdout) => stdout,
            None => {
                terminate_solver_process_group(&mut child, true);
                return Err("failed to capture solver stdout".to_string());
            }
        };

        // Spawn a dedicated reader thread for non-blocking reads.
        // One bounded payload prevents a fast/malformed solver from queueing an
        // unbounded number of individually bounded lines while the verifier is
        // busy between protocol reads.
        let (tx, rx) = mpsc::sync_channel(1);
        let reader_thread = std::thread::Builder::new()
            .name("ay-incremental-stdout-reader".to_string())
            .spawn(move || {
                use std::io::BufReader;
                let mut reader = BufReader::new(stdout);
                loop {
                    match read_bounded_solver_line(&mut reader, MAX_MODEL_OUTPUT_BYTES) {
                        Ok(None) => {
                            let _ = tx.send(Err(
                                "solver closed stdout (process may have crashed)".to_string()
                            ));
                            break;
                        }
                        Ok(Some(line)) => {
                            if tx.send(Ok(line)).is_err() {
                                break;
                            }
                        }
                        Err(error) => {
                            let _ = tx.send(Err(error));
                            break;
                        }
                    }
                }
            });
        if let Err(error) = reader_thread {
            terminate_solver_process_group(&mut child, true);
            return Err(format!("failed to start solver stdout reader: {error}"));
        }

        let mut proc = SolverProcess {
            child,
            group_isolated: true,
            stdin,
            line_rx: rx,
            _reservation: reservation,
        };

        // ay does not implement :print-success and only emits responses for
        // check-sat/get-model-style queries.
        send_command_until(&mut proc, "(set-option :produce-models true)", deadline)?;

        // Trust: deliberately do NOT enable `:produce-proofs`. The pinned ay
        // honors the option by switching `(check-sat)` itself onto its
        // proof-producing lane, which catastrophically degrades queries the
        // plain lane decides instantly (e.g. the symbolic-modulo bound VC:
        // `unsat` in ~60ms without the option, a 30s+ spin with it). Alethe
        // proof capture is documented as purely additive and must never affect
        // a verification verdict, so the session-wide option that changes
        // solving behavior is the wrong lever. The bare incremental `unsat`
        // path therefore never sends `(get-proof)` and remains explicitly
        // Unchecked (see `proved_from_bare_unsat`).

        Ok(proc)
    }

    /// Fall back to per-process verification for a single VC.
    fn verify_per_process(&self, vc: &VerificationCondition) -> VerificationResult {
        let script = smtlib_backend::generate_smtlib_script(&vc.formula);

        // Hold an aggregate-memory reservation for the lifetime of this one-shot
        // solve (acquired before spawn, released when `_reservation` drops at the
        // end of this function). It is inert only when no authority is configured.
        let memory_plan = match self.solver_memory_plan() {
            Ok(plan) => plan,
            Err(reason) => {
                return VerificationResult::Unknown {
                    solver: "ay-incremental-fallback".into(),
                    time_ms: 0,
                    reason,
                };
            }
        };
        let mut reservation = match self.acquire_reservation(&memory_plan) {
            Ok(reservation) => reservation,
            Err(reason) => {
                return VerificationResult::Unknown {
                    solver: "ay-incremental-fallback".into(),
                    time_ms: 0,
                    reason,
                };
            }
        };
        let mut command = Command::new(&self.solver_path);
        command
            .args(&memory_plan.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        isolate_solver_process_group(&mut command);
        if let Err(reason) = reservation.configure_child_lifetime_guard(&mut command) {
            return VerificationResult::Unknown {
                solver: "ay-incremental-fallback".into(),
                time_ms: 0,
                reason: format!("{PRE_SPAWN_LIFETIME_PREFIX} {reason}"),
            };
        }
        let child = match command.spawn() {
            Ok(c) => c,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "ay-incremental-fallback".into(),
                    time_ms: 0,
                    reason: format!("failed to spawn solver: {e}"),
                };
            }
        };
        // Do not let Command's retained pre-exec closure keep the daemon socket
        // alive after the solver and its descendants have exited.
        drop(command);
        // From this point every return path kills/reaps the group before this
        // guard's reservation field can drop.
        let mut child = ReservedSolverChild::new(child, reservation, true);

        let start = Instant::now();

        let stdout = match child.child.stdout.take() {
            Some(stdout) => stdout,
            None => {
                return one_shot_unknown(start, "failed to capture solver stdout".to_string());
            }
        };
        let stderr = match child.child.stderr.take() {
            Some(stderr) => stderr,
            None => {
                return one_shot_unknown(start, "failed to capture solver stderr".to_string());
            }
        };
        let stdout_reader = match spawn_bounded_solver_reader(stdout, "stdout") {
            Ok(reader) => reader,
            Err(reason) => return one_shot_unknown(start, reason),
        };
        let stderr_reader = match spawn_bounded_solver_reader(stderr, "stderr") {
            Ok(reader) => reader,
            Err(reason) => {
                child.terminate_and_reap();
                let _ = join_bounded_solver_reader(stdout_reader, "stdout");
                return one_shot_unknown(start, reason);
            }
        };

        let Some(stdin) = child.child.stdin.take() else {
            child.terminate_and_reap();
            let _ = join_bounded_solver_reader(stdout_reader, "stdout");
            let _ = join_bounded_solver_reader(stderr_reader, "stderr");
            return one_shot_unknown(start, "failed to capture solver stdin".to_string());
        };
        let mut stdin_writer = match spawn_solver_writer(stdin, script.into_bytes()) {
            Ok(writer) => Some(writer),
            Err(reason) => {
                child.terminate_and_reap();
                let _ = join_bounded_solver_reader(stdout_reader, "stdout");
                let _ = join_bounded_solver_reader(stderr_reader, "stderr");
                return one_shot_unknown(start, reason);
            }
        };

        let timeout = Duration::from_millis(self.query_timeout_ms);
        let deadline = start.checked_add(timeout).unwrap_or(start);
        loop {
            match child.exited_without_reaping() {
                Ok(true) => {
                    // Even a normally exited leader may have left same-group
                    // helpers holding pipes/memory. Kill the group while WNOWAIT
                    // still pins its PGID, then reap before releasing capacity.
                    child.terminate_and_reap();
                    break;
                }
                Ok(false) if Instant::now() < deadline => {
                    let remaining = deadline.saturating_duration_since(Instant::now());
                    std::thread::sleep(Duration::from_millis(5).min(remaining));
                }
                Ok(false) => {
                    child.terminate_and_reap();
                    let _ = join_solver_writer(stdin_writer.take().expect("writer is present"));
                    let _ = join_bounded_solver_reader(stdout_reader, "stdout");
                    let _ = join_bounded_solver_reader(stderr_reader, "stderr");
                    return VerificationResult::Timeout {
                        solver: "ay-incremental-fallback".into(),
                        timeout_ms: self.query_timeout_ms,
                    };
                }
                Err(error) => {
                    child.terminate_and_reap();
                    let _ = join_solver_writer(stdin_writer.take().expect("writer is present"));
                    let _ = join_bounded_solver_reader(stdout_reader, "stdout");
                    let _ = join_bounded_solver_reader(stderr_reader, "stderr");
                    return one_shot_unknown(
                        start,
                        format!("failed while waiting for solver: {error}"),
                    );
                }
            }
        }

        let writer_result = join_solver_writer(stdin_writer.take().expect("writer is present"));
        let stdout_result = join_bounded_solver_reader(stdout_reader, "stdout");
        let stderr_result = join_bounded_solver_reader(stderr_reader, "stderr");
        if let Err(reason) = writer_result {
            return one_shot_unknown(start, reason);
        }
        let stdout = match (stdout_result, stderr_result) {
            (Ok(stdout), Ok(_stderr)) => String::from_utf8_lossy(&stdout).to_string(),
            (Err(reason), _) | (_, Err(reason)) => return one_shot_unknown(start, reason),
        };
        let elapsed = start.elapsed().as_millis() as u64;
        smtlib_backend::parse_solver_output(&stdout, elapsed, vec![])
    }
}

impl Default for IncrementalAYSession {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for IncrementalAYSession {
    fn name(&self) -> &str {
        "ay-incremental"
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        matches!(vc.kind.proof_level(), ProofLevel::L0Safety | ProofLevel::L1Functional)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        // VerificationBackend::verify takes &self. The incremental session
        // uses its internal Mutex to manage mutable state, so we can call
        // verify_vc directly (which also takes &self and locks internally).
        self.verify_vc(vc)
    }

    /// Trust: This backend exploits its persistent push/pop context to share a
    /// per-function assertion prefix across a batch, so the router prefers
    /// `verify_batch` when grouping a function's obligations.
    fn supports_shared_prefix_batch(&self) -> bool {
        true
    }

    fn verify_batch(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        // Delegate to the inherent shared-prefix batch (installs each function's
        // prefix at base scope once; verdict-identical to per-VC dispatch).
        IncrementalAYSession::verify_batch(self, vcs)
    }
}

// -- I/O helpers --

/// Send one framed command without allowing a non-reading solver to block past
/// the query's absolute deadline.
fn send_command_until(
    proc: &mut SolverProcess,
    cmd: &str,
    deadline: Instant,
) -> Result<(), String> {
    write_solver_bytes_until(&mut proc.stdin, cmd.as_bytes(), deadline)
        .map_err(|error| format!("write to solver: {error}"))?;
    write_solver_bytes_until(&mut proc.stdin, b"\n", deadline)
        .map_err(|error| format!("write newline to solver: {error}"))
}

#[cfg(unix)]
fn write_solver_bytes_until(
    stdin: &mut std::process::ChildStdin,
    bytes: &[u8],
    deadline: Instant,
) -> std::io::Result<()> {
    use std::os::fd::AsRawFd as _;

    let fd = stdin.as_raw_fd();
    let original_flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if original_flags < 0 {
        return Err(std::io::Error::last_os_error());
    }
    if unsafe { libc::fcntl(fd, libc::F_SETFL, original_flags | libc::O_NONBLOCK) } < 0 {
        return Err(std::io::Error::last_os_error());
    }

    let write_result = (|| {
        let mut written = 0usize;
        while written < bytes.len() {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    "solver stdin write timeout: deadline elapsed",
                ));
            }
            let timeout_ms = remaining
                .as_nanos()
                .saturating_add(999_999)
                .checked_div(1_000_000)
                .unwrap_or(1)
                .min(i32::MAX as u128) as i32;
            let mut descriptor = libc::pollfd { fd, events: libc::POLLOUT, revents: 0 };
            let polled = unsafe { libc::poll(&mut descriptor, 1, timeout_ms) };
            if polled == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    "solver stdin write timeout: deadline elapsed",
                ));
            }
            if polled < 0 {
                let error = std::io::Error::last_os_error();
                if error.kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if descriptor.revents & (libc::POLLERR | libc::POLLHUP | libc::POLLNVAL) != 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::BrokenPipe,
                    "solver closed stdin while a command was being written",
                ));
            }
            if Instant::now() >= deadline {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    "solver stdin write timeout: deadline elapsed",
                ));
            }
            let count = unsafe {
                libc::write(
                    fd,
                    bytes[written..].as_ptr().cast(),
                    bytes.len().saturating_sub(written),
                )
            };
            if count > 0 {
                written = written.saturating_add(count as usize);
                continue;
            }
            if count == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::WriteZero,
                    "solver stdin accepted zero bytes",
                ));
            }
            let error = std::io::Error::last_os_error();
            if matches!(
                error.kind(),
                std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted
            ) {
                continue;
            }
            return Err(error);
        }
        Ok(())
    })();

    let restore = unsafe { libc::fcntl(fd, libc::F_SETFL, original_flags) };
    if restore < 0 && write_result.is_ok() {
        return Err(std::io::Error::last_os_error());
    }
    write_result
}

#[cfg(not(unix))]
fn write_solver_bytes_until(
    _stdin: &mut std::process::ChildStdin,
    _bytes: &[u8],
    _deadline: Instant,
) -> std::io::Result<()> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "deadline-bounded solver stdin writes require Unix poll semantics",
    ))
}

fn one_shot_unknown(start: Instant, reason: String) -> VerificationResult {
    VerificationResult::Unknown {
        solver: "ay-incremental-fallback".into(),
        time_ms: start.elapsed().as_millis() as u64,
        reason,
    }
}

/// Read one incremental protocol line with a hard allocation ceiling. The old
/// `BufRead::read_line` call could grow a `String` without bound before the model
/// aggregate check ever ran.
fn read_bounded_solver_line<R>(reader: &mut R, max_bytes: usize) -> Result<Option<String>, String>
where
    R: std::io::BufRead,
{
    let mut bytes = Vec::with_capacity(256.min(max_bytes));
    let mut limited = reader.take((max_bytes as u64).saturating_add(1));
    let read = std::io::BufRead::read_until(&mut limited, b'\n', &mut bytes)
        .map_err(|error| format!("read from solver: {error}"))?;
    if read == 0 {
        return Ok(None);
    }
    if bytes.len() > max_bytes {
        return Err(format!("solver response line exceeded the {max_bytes} byte limit"));
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|_| "solver response was not valid UTF-8".to_string())
}

fn read_bounded_solver_stream(
    mut reader: impl std::io::Read,
    stream_name: &str,
    max_bytes: usize,
) -> Result<Vec<u8>, String> {
    let mut output = Vec::with_capacity(8192.min(max_bytes));
    reader
        .by_ref()
        .take((max_bytes as u64).saturating_add(1))
        .read_to_end(&mut output)
        .map_err(|error| format!("failed to read solver {stream_name}: {error}"))?;
    if output.len() > max_bytes {
        return Err(format!("solver {stream_name} exceeded the {max_bytes} byte output limit"));
    }
    Ok(output)
}

fn spawn_bounded_solver_reader<R>(
    reader: R,
    stream_name: &'static str,
) -> Result<std::thread::JoinHandle<Result<Vec<u8>, String>>, String>
where
    R: std::io::Read + Send + 'static,
{
    std::thread::Builder::new()
        .name(format!("ay-{stream_name}-reader"))
        .spawn(move || read_bounded_solver_stream(reader, stream_name, MAX_MODEL_OUTPUT_BYTES))
        .map_err(|error| format!("failed to start solver {stream_name} reader: {error}"))
}

fn spawn_solver_writer(
    mut stdin: std::process::ChildStdin,
    input: Vec<u8>,
) -> Result<std::thread::JoinHandle<Result<(), String>>, String> {
    std::thread::Builder::new()
        .name("ay-oneshot-stdin-writer".to_string())
        .spawn(move || {
            stdin
                .write_all(&input)
                .map_err(|error| format!("failed to write to solver stdin: {error}"))
        })
        .map_err(|error| format!("failed to start solver stdin writer: {error}"))
}

fn join_solver_writer(writer: std::thread::JoinHandle<Result<(), String>>) -> Result<(), String> {
    writer.join().map_err(|_| "solver stdin writer panicked".to_string())?
}

fn join_bounded_solver_reader(
    reader: std::thread::JoinHandle<Result<Vec<u8>, String>>,
    stream_name: &'static str,
) -> Result<Vec<u8>, String> {
    reader.join().map_err(|_| format!("solver {stream_name} reader panicked"))?
}

/// Compute remaining timeout from a deadline.
fn remaining_timeout(total: Duration, start: Instant) -> Duration {
    let elapsed = start.elapsed();
    if elapsed >= total { Duration::from_millis(1) } else { total - elapsed }
}

/// Read a single response line from the solver.
/// Whether a solver stdout line is a non-response comment to be skipped.
///
/// ay frames every session with DIMACS-style `c ` banner lines
/// (`c ay.session.start …` at startup, `c ay.session.end …` at exit), and
/// SMT-LIB permits `;`-prefixed comments. Neither is a command response, so
/// the incremental protocol must skip them — otherwise the startup banner is
/// read as the first `(check-sat)` verdict and every later read is shifted by
/// one line, degrading every VC to Unknown.
fn is_solver_comment_line(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed == "c" || trimmed.starts_with("c ") || trimmed.starts_with(';')
}

fn read_response_line(proc: &mut SolverProcess, timeout: Duration) -> Result<String, String> {
    let start = Instant::now();
    loop {
        if start.elapsed() >= timeout {
            return Err(SolverProcessError::Timeout {
                solver: "ay-incremental",
                detail: "no response within deadline".to_string(),
            }
            .to_string());
        }
        match proc.line_rx.recv_timeout(remaining_timeout(timeout, start)) {
            Ok(Ok(line)) => {
                if line.is_empty() {
                    return Err(SolverProcessError::ProcessCrashed {
                        solver: "ay-incremental",
                        detail: "solver closed stdout".to_string(),
                    }
                    .to_string());
                }
                if is_solver_comment_line(&line) {
                    // Skip a session banner / comment and keep reading for the
                    // actual response.
                    continue;
                }
                return Ok(line);
            }
            Ok(Err(e)) => return Err(e),
            Err(mpsc::RecvTimeoutError::Timeout) => {
                return Err(SolverProcessError::Timeout {
                    solver: "ay-incremental",
                    detail: "no response within deadline".to_string(),
                }
                .to_string());
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err(SolverProcessError::Disconnected {
                    solver: "ay-incremental",
                    detail: "reader thread disconnected".to_string(),
                }
                .to_string());
            }
        }
    }
}

/// Read a multi-line model response from the solver.
fn read_model_response(proc: &mut SolverProcess, timeout: Duration) -> Result<String, String> {
    let mut output = String::new();
    let mut depth: i32 = 0;
    let mut started = false;
    let start = Instant::now();

    loop {
        if start.elapsed() >= timeout {
            return Err(SolverProcessError::Timeout {
                solver: "ay-incremental",
                detail: "timeout during model read".to_string(),
            }
            .to_string());
        }
        let remaining = remaining_timeout(timeout, start);
        let line = match proc.line_rx.recv_timeout(remaining) {
            Ok(Ok(line)) => line,
            Ok(Err(e)) => return Err(e),
            Err(mpsc::RecvTimeoutError::Timeout) => {
                return Err(SolverProcessError::Timeout {
                    solver: "ay-incremental",
                    detail: "timeout during model read".to_string(),
                }
                .to_string());
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err(SolverProcessError::Disconnected {
                    solver: "ay-incremental",
                    detail: "disconnected during model read".to_string(),
                }
                .to_string());
            }
        };

        if line.is_empty() {
            return Err(SolverProcessError::ProcessCrashed {
                solver: "ay-incremental",
                detail: "solver closed stdout during model read".to_string(),
            }
            .to_string());
        }

        for ch in line.chars() {
            match ch {
                '(' => {
                    depth += 1;
                    started = true;
                }
                ')' => depth -= 1,
                _ => {}
            }
        }

        let attempted_bytes = output.len().saturating_add(line.len());
        if attempted_bytes > MAX_MODEL_OUTPUT_BYTES {
            return Err(SolverProcessError::ModelOutputTooLarge {
                solver: "ay-incremental",
                bytes: attempted_bytes,
                limit: MAX_MODEL_OUTPUT_BYTES,
            }
            .to_string());
        }
        output.push_str(&line);

        if started && depth <= 0 {
            break;
        }
    }

    Ok(output)
}

/// Trust: The DECLARATION IDENTITY of an SMT-LIB2 declaration command — the
/// name it introduces into the solver's namespace.
///
/// Handles every declaration shape `smt2_export::emit_declarations` can emit:
///
/// * `(declare-fun name () Sort)` / `(declare-fun name (Sorts) Bool)`
/// * `(declare-const name Sort)`
/// * `(declare-sort name 0)` — Lever A's by-name datatype back-edge
/// * `(declare-datatype name ((Ctor (field Sort)) …))` — Lever A's inductive
///   datatype preamble
///
/// The name is what the base-scope/per-VC-scope de-duplication keys on:
/// re-declaring inside `(push 1)` something already bound at the enclosing base
/// scope is an error for most solvers, which errors the session, forces a
/// process restart, and (after `MAX_CONSECUTIVE_FAILURES`) permanently falls
/// the session back to per-process mode. A `declare-sort`/`declare-datatype`
/// carries EXACTLY that hazard — a datatype-bearing prefix and its per-VC
/// obligations both emit the same `(declare-datatype Expr …)` — so sorts are
/// keyed the same way as variables, not ignored.
///
/// Returns `None` for any non-declaration command (assertions, `set-logic`, …).
fn extract_declared_name(decl: &str) -> Option<String> {
    let trimmed = decl.trim();
    for prefix in ["(declare-fun ", "(declare-const ", "(declare-sort ", "(declare-datatype "] {
        if let Some(rest) = trimmed.strip_prefix(prefix) {
            let end = rest.find(|c: char| c.is_whitespace())?;
            return Some(rest[..end].to_string());
        }
    }
    None
}

/// Trust: True for a declaration that introduces a SORT name (`declare-sort` /
/// `declare-datatype`) rather than a value symbol (`declare-fun` /
/// `declare-const`).
///
/// Ordering matters for sorts and not for values: a `(declare-fun e () Expr)`
/// is malformed unless `Expr` is already declared, and a datatype whose field
/// sort is another datatype must follow that one. `emit_declarations` emits
/// sorts first, topologically ordered; any code that REORDERS declarations must
/// preserve that, which is what this predicate is for.
fn declares_sort(decl: &str) -> bool {
    let trimmed = decl.trim();
    trimmed.starts_with("(declare-sort ") || trimmed.starts_with("(declare-datatype ")
}

/// Trust: The declarations the per-VC push scope must send for `formula`, given
/// the names already declared at the enclosing base scope.
///
/// A declaration whose identity is already bound at the base scope is SKIPPED:
/// the base binding is in scope inside `(push 1)`, so the VC's assertion still
/// resolves the name, while re-declaring it would error the session. This is
/// the single place the skip rule lives, so the base-scope snapshot
/// (`SessionState::prefix_declared_vars`) and the per-VC emission can never
/// drift apart.
fn scope_declarations(
    formula: &Formula,
    base_declared: &std::collections::HashSet<String>,
) -> Vec<String> {
    smt2_export::emit_declarations(formula)
        .into_iter()
        .filter(|decl| {
            !extract_declared_name(decl).is_some_and(|name| base_declared.contains(&name))
        })
        .collect()
}

/// Trust: Detect an SMT logic wide enough for EVERY VC in a function group.
///
/// `detect_logic` is monotone in formula features, so the logic that covers the
/// union of all the group's full formulas is correct for each individual member
/// (and for the shared prefix, whose conjuncts are a subset of each member). We
/// compute it by analyzing each VC's formula and keeping the richest logic
/// observed — concretely, the logic of `And([all group formulas])`.
fn detect_group_logic(group_vcs: &[VerificationCondition]) -> String {
    match group_vcs.len() {
        0 => smt2_export::detect_logic(&Formula::Bool(true)).to_string(),
        1 => smt2_export::detect_logic(&group_vcs[0].formula).to_string(),
        _ => {
            let all =
                Formula::And(group_vcs.iter().map(|vc| vc.formula.clone()).collect::<Vec<_>>());
            smt2_export::detect_logic(&all).to_string()
        }
    }
}

/// Trust: Flatten the top-level conjunction of a formula into its conjuncts.
///
/// `And([a, And([b, c]), d])` flattens to `[a, b, c, d]`; a non-`And` formula
/// `f` yields `[f]`; `And([])` yields `[]`. Flattening is sound because `And` is
/// associative.
fn flatten_conjuncts(formula: &Formula) -> Vec<Formula> {
    fn go(f: &Formula, out: &mut Vec<Formula>) {
        match f {
            Formula::And(terms) => terms.iter().for_each(|t| go(t, out)),
            other => out.push(other.clone()),
        }
    }
    let mut out = Vec::new();
    go(formula, &mut out);
    out
}

/// Trust: Re-wrap conjuncts into a single formula (identity of conjunction for
/// the empty list; bare conjunct for a singleton; `And` otherwise).
fn conjoin_formulas(mut conjuncts: Vec<Formula>) -> Formula {
    match conjuncts.len() {
        0 => Formula::Bool(true),
        1 => conjuncts.pop().expect("len checked == 1"),
        _ => Formula::And(conjuncts),
    }
}

/// Trust: Compute the per-function shared assertion prefix and rewrite each VC
/// to carry only its bare (prefix-free) obligation.
///
/// Returns `(prefix, bare_vcs)` where `prefix` is the list of top-level
/// conjuncts present (by structural equality) in EVERY input VC — in first-VC
/// order, de-duplicated — and `bare_vcs` is the inputs with `formula` replaced
/// by the conjunction of their NON-prefix conjuncts (all other fields
/// preserved).
///
/// # Equivalence
///
/// For each `i`: `And(prefix ++ flatten(bare_vcs[i].formula)) ≡ vcs[i].formula`
/// as a logical value. `prefix` is a subset of `vcs[i]`'s own conjuncts (it is
/// the intersection across the group), and `bare_vcs[i]` is `vcs[i]`'s conjuncts
/// minus the prefix; their union as a SET is `vcs[i]`'s conjunct set, and `And`
/// is commutative + associative + idempotent, so the conjunction VALUE (hence
/// the solver's model set and verdict) is unchanged.
///
/// This mirrors `trust_vcgen::shared_prefix::split_shared_prefix`; the logic is
/// duplicated here because `trust-router` does not depend on `trust-vcgen` in
/// its build graph (only as a dev-dependency).
fn split_shared_prefix(
    vcs: &[VerificationCondition],
) -> (Vec<Formula>, Vec<VerificationCondition>) {
    if vcs.is_empty() {
        return (Vec::new(), Vec::new());
    }

    let first_conjuncts = flatten_conjuncts(&vcs[0].formula);

    // Per-VC presence sets (flattened, so nested `And`s register too).
    let presence: Vec<std::collections::HashSet<Formula>> =
        vcs.iter().map(|vc| flatten_conjuncts(&vc.formula).into_iter().collect()).collect();

    // A candidate is shared iff present in every VC. Preserve first-VC order;
    // de-duplicate (one prefix copy suffices — `A ∧ A ≡ A`).
    let mut prefix: Vec<Formula> = Vec::new();
    let mut prefix_set: std::collections::HashSet<Formula> = std::collections::HashSet::new();
    for cand in &first_conjuncts {
        if prefix_set.contains(cand) {
            continue;
        }
        if presence.iter().all(|p| p.contains(cand)) {
            prefix_set.insert(cand.clone());
            prefix.push(cand.clone());
        }
    }

    // Drop ALL prefix occurrences from each VC (the base scope re-supplies one).
    let bare_vcs: Vec<VerificationCondition> = vcs
        .iter()
        .map(|vc| {
            let remaining: Vec<Formula> = flatten_conjuncts(&vc.formula)
                .into_iter()
                .filter(|c| !prefix_set.contains(c))
                .collect();
            let mut bare = vc.clone();
            bare.formula = conjoin_formulas(remaining);
            bare
        })
        .collect();

    (prefix, bare_vcs)
}

/// A literal constant (no free variables, decidable on its own).
fn is_constant_formula(f: &Formula) -> bool {
    matches!(f, Formula::Int(_) | Formula::UInt(_) | Formula::Bool(_) | Formula::BitVec { .. })
}

/// Replace every NONLINEAR atom in `formula` with a fresh, unconstrained variable
/// of the same sort, returning the relaxed formula — or `None` if there was no
/// nonlinear atom to relax (so the caller skips a pointless re-query).
///
/// Nonlinear atoms: `Rem`/`Div` by a non-constant divisor, `Mul` of two
/// non-constant factors, and the bitvector analogues (`BvURem`/`BvSRem`/`BvUDiv`/
/// `BvSDiv` by a non-constant, `BvMul` of two non-constants). Division/remainder by
/// a CONSTANT and multiplication by a CONSTANT stay (they are linear and the solver
/// handles them). `Formula::map` is post-order, so a nested term's children are
/// already relaxed when its parent is examined.
///
/// SOUND RELAXATION: each fresh variable is unconstrained, so the relaxed formula
/// has a superset of the original's satisfying assignments; therefore
/// `relaxed UNSAT ⟹ original UNSAT`. See [`IncrementalAYSession::relax_if_unknown`].
fn abstract_nonlinear(formula: &Formula) -> Option<Formula> {
    let mut counter: usize = 0;
    let mut fresh = |sort: Sort| {
        counter += 1;
        Formula::Var(format!("__relax_nl_{counter}"), sort)
    };
    let relaxed = formula.clone().map(&mut |f| match &f {
        Formula::Rem(_, b) | Formula::Div(_, b) if !is_constant_formula(b) => fresh(Sort::Int),
        Formula::Mul(a, b) if !is_constant_formula(a) && !is_constant_formula(b) => {
            fresh(Sort::Int)
        }
        Formula::BvURem(_, b, w)
        | Formula::BvSRem(_, b, w)
        | Formula::BvUDiv(_, b, w)
        | Formula::BvSDiv(_, b, w)
            if !is_constant_formula(b) =>
        {
            fresh(Sort::BitVec(*w))
        }
        Formula::BvMul(a, b, w) if !is_constant_formula(a) && !is_constant_formula(b) => {
            fresh(Sort::BitVec(*w))
        }
        _ => f,
    });
    (counter > 0).then_some(relaxed)
}

/// Witness-backed refutation for any VC whose failure formula contains a
/// symbolic multiplication (`Mul` or `BvMul` of two non-constant variables).
///
/// The gap this closes: a failure formula like `count >= CEILING AND
/// count == s * s * 12` is QF_NIA — the product of two runtime vars makes the
/// theory undecidable, so `ay` returns `unknown` and the obligation is never
/// refuted, even though concrete `s` values that overflow the ceiling clearly
/// exist (the nn flash-attn O(S^2) shape). Rather than ask the solver to *prove*
/// nonlinear sat, we *exhibit* a concrete model: pick witness values for the two
/// mul operands, plug them into [`eval_bool_formula`], and if the WHOLE failure
/// formula (path guards, type ranges, preconditions, and the ceiling test
/// included) concretely evaluates to `true`, that assignment is a sound
/// counterexample and the verdict is `Failed`.
///
/// Witness values are KIND-AWARE but the search machinery is shared:
///   - `ArithmeticOverflow { op: Mul }`: drive the product past `2^width` (type
///     overflow) — the original, unchanged behavior.
///   - everything else (notably `UnboundedAllocation`): drive the product over
///     the allocation CEILING `K` extracted from a `Ge(_, K)` / `Gt(_, K)` atom.
///
/// Sound by construction: we only ever return `Failed` when a *concrete* model
/// satisfies the failure formula, so a SAFE (guarded / sub-ceiling) VC is never
/// spuriously failed — its guards make `eval_bool_formula` return `Some(false)`.
/// A VC with no symbolic mul produces no candidate pairs and is left untouched.
/// The search is bounded (a fixed witness ladder × the deduped pair list).
fn mul_counterexample(vc: &VerificationCondition) -> Option<VerificationResult> {
    let pairs = mul_var_pairs(&vc.formula);
    if pairs.is_empty() {
        return None;
    }

    // The witness value-pairs to try, in priority order, and whether the
    // reported counterexample values are signed.
    let (signed, candidates) = mul_witness_candidates(vc);
    if candidates.is_empty() {
        return None;
    }

    for (lhs_name, rhs_name) in pairs {
        for &(lhs_value, rhs_value) in &candidates {
            let mut env = std::collections::BTreeMap::new();
            env.insert(lhs_name.clone(), Formula::Int(lhs_value));
            env.insert(rhs_name.clone(), Formula::Int(rhs_value));
            // The mul operands are the only free vars we choose; intermediate
            // vars (e.g. `count == s * s * 12`) are PINNED by equations in the
            // formula. Propagate those equalities so the ceiling test, which is
            // written over `count`, becomes concrete. Sound: each added binding
            // equals the value its own `x == expr` constraint forces.
            propagate_equalities(&vc.formula, &mut env);
            if eval_bool_formula(&vc.formula, &env) == Some(true) {
                let value = |n: i128| {
                    if signed {
                        CounterexampleValue::Int(n)
                    } else {
                        CounterexampleValue::Uint(n as u128)
                    }
                };
                return Some(VerificationResult::Failed {
                    solver: "ay-incremental-witness".into(),
                    time_ms: 0,
                    counterexample: Some(Counterexample::new(vec![
                        (lhs_name, value(lhs_value)),
                        (rhs_name, value(rhs_value)),
                    ])),
                });
            }
        }
    }

    None
}

/// Bounded equality propagation. For every `Eq(Var(x), expr)` (either
/// orientation) reachable in `formula` whose `expr` evaluates to a concrete
/// integer under the current `env` and whose `x` is not yet bound, bind
/// `x -> value`. Repeat to a fixpoint so chained definitions
/// (`a == s*2`, `count == a*6`) resolve. Bounded by the number of distinct
/// variables (each pass binds at least one new var or stops), so it terminates.
///
/// SOUND: an `x == expr` atom is a CONSTRAINT in the conjoined failure formula;
/// binding `x` to the value `expr` already takes is the unique value consistent
/// with that constraint, so it never enlarges the set of satisfying assignments —
/// it only completes the partial model the caller is testing.
fn propagate_equalities(formula: &Formula, env: &mut std::collections::BTreeMap<String, Formula>) {
    let mut eqs = Vec::new();
    collect_var_equalities(formula, &mut eqs);
    // At most one new binding can be discovered per (eq), so capping the outer
    // loop at the equation count is a sound, generous fixpoint bound.
    for _ in 0..=eqs.len() {
        let mut changed = false;
        for (name, expr) in &eqs {
            if env.contains_key(name) {
                continue;
            }
            if let Some(v) = eval_int_formula(expr, env) {
                env.insert(name.clone(), Formula::Int(v));
                changed = true;
            } else if let Some(b) = eval_bool_formula(expr, env) {
                // Trust: pin a bool-sorted temp (`flag == (count >= ceiling)`) so a
                // violation flowing through a bool block-def still folds to forced.
                env.insert(name.clone(), Formula::Bool(b));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Collect `(var_name, defining_expr)` for every `Eq(Var(x), expr)` /
/// `Eq(expr, Var(x))` atom anywhere in `formula` (where the other side is not
/// itself a bare variable, to avoid binding a var to another unbound var).
///
/// SOUNDNESS (forced-violation classification): when an `Eq(Var(x), expr)` IS
/// collected as `x`'s definition, we MUST NOT then recurse INTO `expr` to harvest a
/// nested `Eq(Var(y), const)` as a *binding* for `y`. Inside `x`'s definition that
/// nested equality is a boolean COMPARISON OPERAND (it computes a bool), not a
/// standalone definitional fact about `y` — `y` may be a genuinely FREE input. The
/// `|v| -v` closure's negation VC is exactly this shape: `_3 = (v == i64::MIN) ∧ _3`,
/// where binding `v := i64::MIN` from the nested `v == MIN` would make a merely
/// POSSIBLE (free-`v`-dependent) violation fold to forced-true and be FALSE-escalated
/// to a guaranteed Level-0 error on provably-safe code. Skipping the recursion into a
/// collected binding's defining `expr` keeps `v` free, so the violation correctly
/// stays a (possible) warning. This can only ever REMOVE a binding, so it can never
/// make a non-forced violation look forced — it strictly tightens the forced test
/// toward fewer false escalations (sound: never a false PROVE, never a false
/// guaranteed-violation).
fn collect_var_equalities<'a>(formula: &'a Formula, out: &mut Vec<(String, &'a Formula)>) {
    if let Formula::Eq(lhs, rhs) = formula {
        match (formula_var_name(lhs), formula_var_name(rhs)) {
            // `x == expr` where expr is not a bare var. `expr` is `x`'s definition;
            // do NOT descend into it (its nested `Eq`s are comparison operands, not
            // standalone bindings) — only recurse into the OTHER side (a bare var,
            // which has no sub-equalities to harvest).
            (Some(name), None) => {
                out.push((name, rhs));
                return;
            }
            (None, Some(name)) => {
                out.push((name, lhs));
                return;
            }
            _ => {}
        }
    }
    for child in formula.children() {
        collect_var_equalities(child, out);
    }
}

/// Build the (signedness, witness value-pairs) to try for `vc`, dispatched on
/// `VcKind`. Each pair `(a, b)` is plugged into both mul operands by the caller.
fn mul_witness_candidates(vc: &VerificationCondition) -> (bool, Vec<(i128, i128)>) {
    match &vc.kind {
        // Type overflow: drive the product past 2^width. Unchanged behavior.
        VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (lhs_ty, rhs_ty) } => {
            if lhs_ty != rhs_ty {
                return (false, Vec::new());
            }
            let Some(width) = lhs_ty.int_width() else {
                return (false, Vec::new());
            };
            if width > 63 {
                return (false, Vec::new());
            }
            let signed = lhs_ty.is_signed();
            let values = mul_overflow_witness_values(width, signed)
                .map(|pair| vec![pair])
                .unwrap_or_default();
            (signed, values)
        }
        // Allocation ceiling (and any other kind with a symbolic mul): drive the
        // product over the threshold K extracted from the failure formula.
        _ => (false, ceiling_witness_values(&vc.formula)),
    }
}

/// Candidate witness pairs that aim to push a `Mul` product over an allocation
/// CEILING. The ceiling `K` is read off the failure formula's `Ge(_, K)` /
/// `Gt(_, K)` atoms (the `count >= CEILING` test). For each such `K`, propose:
///   - the SYMMETRIC witness `a == b == ceil(sqrt(K))` (and a small ladder above
///     it), which covers `s * s * c >= K` shapes like flash-attn's `s*s*12`; and
///   - the ASYMMETRIC witness `a == K, b == 2`, which covers `a * b >= K` where
///     the two factors are independent.
///
/// Values are kept well within `i128` so the checked arithmetic in
/// [`eval_int_formula`] never overflows (the largest meaningful ceiling here is
/// AY's `1 << 28` element backstop). All proposals are *candidates*; only those
/// that make the WHOLE formula evaluate to `true` are accepted by the caller.
fn ceiling_witness_values(formula: &Formula) -> Vec<(i128, i128)> {
    let mut ceilings = Vec::new();
    collect_ceiling_thresholds(formula, &mut ceilings);
    ceilings.sort_unstable();
    ceilings.dedup();

    let mut out = Vec::new();
    for &k in &ceilings {
        if k <= 0 {
            continue;
        }
        // Symmetric root + a short ladder so `c * a * a >= K` clears even when a
        // small leading coefficient `c` is folded into the product.
        let root = isqrt_i128(k);
        for delta in 0..=4i128 {
            if let Some(a) = root.checked_add(delta) {
                out.push((a, a));
            }
        }
        // Asymmetric: one factor at the ceiling, the other a small multiplier.
        out.push((k, 2));
        out.push((k, k));
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Collect the right-hand constant `K` of every `Ge(_, K)` / `Gt(_, K)` atom
/// (the allocation-ceiling test lives in this shape) anywhere in `formula`.
fn collect_ceiling_thresholds(formula: &Formula, out: &mut Vec<i128>) {
    match formula {
        Formula::Ge(_, rhs) | Formula::Gt(_, rhs) => {
            if let Some(k) = constant_int_value(rhs) {
                out.push(k);
            }
        }
        // Also handle `K <= count` / `K < count` written the other way around.
        Formula::Le(lhs, _) | Formula::Lt(lhs, _) => {
            if let Some(k) = constant_int_value(lhs) {
                out.push(k);
            }
        }
        _ => {}
    }
    for child in formula.children() {
        collect_ceiling_thresholds(child, out);
    }
}

/// Integer literal value of `f` (`Int`/`UInt`/`BitVec`), else `None`.
fn constant_int_value(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => i128::try_from(*v).ok(),
        Formula::BitVec { value, .. } => Some(*value),
        _ => None,
    }
}

/// Integer square root (floor) for non-negative `i128`. Bounded, no float.
fn isqrt_i128(n: i128) -> i128 {
    if n < 2 {
        return n.max(0);
    }
    let mut lo: i128 = 1;
    let mut hi: i128 = 1i128 << 63; // sqrt(i128::MAX) < 2^63; safe upper bound.
    while lo < hi {
        let mid = lo + (hi - lo + 1) / 2;
        if let Some(sq) = mid.checked_mul(mid)
            && sq <= n
        {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

fn mul_overflow_witness_values(width: u32, signed: bool) -> Option<(i128, i128)> {
    if signed {
        let max = if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        (max > 1).then_some((max, 2))
    } else {
        let max = (1i128 << width) - 1;
        let base = 1i128 << width.div_ceil(2);
        (base.checked_mul(base)? > max).then_some((base, base))
    }
}

fn mul_var_pairs(formula: &Formula) -> Vec<(String, String)> {
    let mut pairs = Vec::new();
    collect_mul_var_pairs(formula, &mut pairs);
    pairs.sort();
    pairs.dedup();
    pairs
}

fn collect_mul_var_pairs(formula: &Formula, pairs: &mut Vec<(String, String)>) {
    // Both the unbounded-integer `Mul` and the fixed-width `BvMul` of two
    // non-constant variables are symbolic multiplications that send the theory
    // to QF_NIA / QF_BV-nonlinear — both are witness-able the same way.
    let factors = match formula {
        Formula::Mul(lhs, rhs) | Formula::BvMul(lhs, rhs, _) => Some((lhs, rhs)),
        _ => None,
    };
    if let Some((lhs, rhs)) = factors
        && let (Some(lhs_name), Some(rhs_name)) = (formula_var_name(lhs), formula_var_name(rhs))
    {
        pairs.push((lhs_name, rhs_name));
    }
    for child in formula.children() {
        collect_mul_var_pairs(child, pairs);
    }
}

fn formula_var_name(formula: &Formula) -> Option<String> {
    match formula {
        // Trust: recognize a variable of ANY sort (Int/BitVec/Bool/...). Bool
        // coverage lets equality-propagation pin a block-def bool temp
        // (`flag == (count >= ceiling)`); the mul-witness is unaffected since
        // `Mul`/`BvMul` operands are never bool.
        Formula::Var(name, _) => Some(name.clone()),
        Formula::SymVar(symbol, _) => Some(symbol.to_string()),
        _ => None,
    }
}

fn eval_bool_formula(
    formula: &Formula,
    env: &std::collections::BTreeMap<String, Formula>,
) -> Option<bool> {
    match formula {
        Formula::Bool(value) => Some(*value),
        Formula::Not(inner) => eval_bool_formula(inner, env).map(|value| !value),
        Formula::And(terms) => {
            let mut saw_unknown = false;
            for term in terms {
                match eval_bool_formula(term, env) {
                    Some(true) => {}
                    Some(false) => return Some(false),
                    None => saw_unknown = true,
                }
            }
            (!saw_unknown).then_some(true)
        }
        Formula::Or(terms) => {
            let mut saw_unknown = false;
            for term in terms {
                match eval_bool_formula(term, env) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => saw_unknown = true,
                }
            }
            (!saw_unknown).then_some(false)
        }
        Formula::Implies(lhs, rhs) => match eval_bool_formula(lhs, env) {
            Some(false) => Some(true),
            Some(true) => eval_bool_formula(rhs, env),
            None => None,
        },
        Formula::Eq(lhs, rhs) => {
            if let (Some(lhs), Some(rhs)) = (eval_int_formula(lhs, env), eval_int_formula(rhs, env))
            {
                Some(lhs == rhs)
            } else {
                match (eval_bool_formula(lhs, env), eval_bool_formula(rhs, env)) {
                    (Some(lhs), Some(rhs)) => Some(lhs == rhs),
                    _ => None,
                }
            }
        }
        Formula::Lt(lhs, rhs) => Some(eval_int_formula(lhs, env)? < eval_int_formula(rhs, env)?),
        Formula::Le(lhs, rhs) => Some(eval_int_formula(lhs, env)? <= eval_int_formula(rhs, env)?),
        Formula::Gt(lhs, rhs) => Some(eval_int_formula(lhs, env)? > eval_int_formula(rhs, env)?),
        Formula::Ge(lhs, rhs) => Some(eval_int_formula(lhs, env)? >= eval_int_formula(rhs, env)?),
        // Trust: a bool-sorted variable resolves through the propagated env, so a
        // block-def-pinned bool temp (`flag == (count >= ceiling)`) evaluates and a
        // violation flowing through it can fold to a constant.
        Formula::Var(name, _) => eval_bool_formula(env.get(name)?, env),
        Formula::SymVar(symbol, _) => eval_bool_formula(env.get(symbol.as_str())?, env),
        _ => None,
    }
}

fn eval_int_formula(
    formula: &Formula,
    env: &std::collections::BTreeMap<String, Formula>,
) -> Option<i128> {
    match formula {
        Formula::Int(value) => Some(*value),
        Formula::UInt(value) => i128::try_from(*value).ok(),
        Formula::BitVec { value, .. } => Some(*value),
        Formula::Var(name, Sort::Int) => eval_int_formula(env.get(name)?, env),
        Formula::SymVar(symbol, Sort::Int) => eval_int_formula(env.get(symbol.as_str())?, env),
        Formula::Add(lhs, rhs) => {
            eval_int_formula(lhs, env)?.checked_add(eval_int_formula(rhs, env)?)
        }
        Formula::Sub(lhs, rhs) => {
            eval_int_formula(lhs, env)?.checked_sub(eval_int_formula(rhs, env)?)
        }
        Formula::Mul(lhs, rhs) => {
            eval_int_formula(lhs, env)?.checked_mul(eval_int_formula(rhs, env)?)
        }
        Formula::Div(lhs, rhs) => {
            eval_int_formula(lhs, env)?.checked_div(eval_int_formula(rhs, env)?)
        }
        Formula::Rem(lhs, rhs) => {
            eval_int_formula(lhs, env)?.checked_rem(eval_int_formula(rhs, env)?)
        }
        Formula::Neg(inner) => eval_int_formula(inner, env)?.checked_neg(),
        Formula::Ite(cond, then_value, else_value) => {
            if eval_bool_formula(cond, env)? {
                eval_int_formula(then_value, env)
            } else {
                eval_int_formula(else_value, env)
            }
        }
        // Trust: fold CONSTANT bit-vector round-trips so a const shift/mask count
        // (`1 << 28` lowered through IntToBv/BvShl/BvAnd/BvToInt) resolves to a
        // concrete value. Bounded to widths <= 64; wider widths bail to `None`
        // (sound — only leaves a count un-foldable, never wrongly forced).
        Formula::IntToBv(inner, w) => bv_mask(eval_int_formula(inner, env)?, *w),
        Formula::BvAnd(lhs, rhs, w) => {
            bv_mask(eval_int_formula(lhs, env)? & eval_int_formula(rhs, env)?, *w)
        }
        Formula::BvShl(lhs, rhs, w) => {
            let a = eval_int_formula(lhs, env)?;
            let b = eval_int_formula(rhs, env)?;
            if b < 0 || b >= i128::from(*w) {
                bv_mask(0, *w)
            } else {
                bv_mask(a.checked_shl(u32::try_from(b).ok()?)?, *w)
            }
        }
        Formula::BvToInt(inner, w, signed) => {
            let u = bv_mask(eval_int_formula(inner, env)?, *w)?;
            if *signed && *w >= 1 && *w <= 64 && u >= (1i128 << (*w - 1)) {
                Some(u - (1i128 << *w))
            } else {
                Some(u)
            }
        }
        _ => None,
    }
}

/// Trust: low `w` bits of `v` as an UNSIGNED value, for `1 <= w <= 64`. `None`
/// for `w == 0`/`w > 64`, keeping the mask in i128 range (sound: unrepresentable
/// widths stay un-foldable, never wrongly forced).
fn bv_mask(v: i128, w: u32) -> Option<i128> {
    if w == 0 || w > 64 {
        return None;
    }
    Some(v & ((1i128 << w) - 1))
}

/// Trust: a Level-0 safety VIOLATION is GUARANTEED (sound to hard-error in the
/// default lane) iff its VC formula evaluates to `true` after propagating the
/// block-def equalities (Int AND Bool) to a fixpoint — every relevant variable is
/// forced to a constant and the violation holds unconditionally. A constant bulk
/// allocation (`count == 1<<28 AND count >= 1<<28`, possibly via a bool temp)
/// folds to forced-`true`; an input-dependent `a + b > MAX` cannot fold (a, b
/// free) and is merely POSSIBLE, not guaranteed. Independent of the forward
/// solver verdict, so it ALSO catches a trivial ground violation the solver could
/// only return `unknown` for.
#[must_use]
pub fn violation_is_forced(formula: &Formula) -> bool {
    let mut env = std::collections::BTreeMap::new();
    propagate_equalities(formula, &mut env);
    eval_bool_formula(formula, &env) == Some(true)
}

/// Trust: `true` iff `formula` is a bare `true` LITERAL — a vcgen MODELING-GAP
/// FAIL-CLOSE marker, NOT a violation forced by the program's own modeled values.
///
/// SOUNDNESS RATIONALE (the discriminator that keeps the guaranteed-violation
/// hard error honest): several vcgen paths emit a literal `Formula::Bool(true)`
/// as a deliberately fail-closed obligation when they CANNOT MODEL the relevant
/// fact — e.g. the `Index<Range>` body when the receiver's length is unresolved
/// or its range aggregate is untraceable (`generate::panic_calls`, "Untraceable
/// range — already the `Bool(true)` fail-close"), an FFI boundary with no
/// summary, or a memory-provenance gap. Keeping such an obligation FAILED (so the
/// warning / coverage lane and the strict full-verification abort still surface
/// it) is correct. But a bare `Bool(true)` carries ZERO information about the
/// program's actual values: the indexed code may be provably in-bounds
/// (`bytes[52..56]` on a `[u8; 64]` whose `&[T; N]` length the model did not
/// recover), so reporting it as a GUARANTEED, every-execution Level-0 VIOLATION
/// is a FALSE REFUTATION of correct code. A genuine value-forced violation always
/// folds through REAL modeled atoms (`Ge(1<<28, 1<<28)`, `Ge(100, 64)`) — never a
/// bare literal — so excluding the bare-literal case from that escalation removes
/// only false refutations. Fail-closed: the obligation stays FAILED, never PROVED
/// (`violation_is_modeling_gap_failclose` is only ever consulted to WITHHOLD an
/// escalation, never to grant a proof).
#[must_use]
pub fn violation_is_modeling_gap_failclose(formula: &Formula) -> bool {
    matches!(formula, Formula::Bool(true))
}

/// Trust: an `UnboundedAllocation` is a GUARANTEED over-budget violation iff its
/// COUNT folds to a compile-time constant at or above the budget ceiling — i.e.
/// the violation atom `Ge(count, CEILING)` / `Gt(count, CEILING)` holds with
/// `count` forced — REGARDLESS of reaching guards. The allocation SITE, when
/// reached, allocates that constant over-budget amount; reaching guards (a
/// shift's panic-freedom, a branch condition — often carrying a free var like a
/// shift amount vcgen leaves unpinned) only decide WHEN it is reached, not
/// WHETHER it is over-budget. Soundness: anchored at `ALLOC_CEILING`, so a small
/// guard threshold (`_2 < 64`) cannot match; and an input-dependent count
/// (`with_capacity(a+b)`) does not fold, so it stays a warning.
#[must_use]
pub fn alloc_over_ceiling_forced(formula: &Formula) -> bool {
    let mut env = std::collections::BTreeMap::new();
    propagate_equalities(formula, &mut env);
    alloc_violation_holds(formula, &env)
}

fn alloc_violation_holds(f: &Formula, env: &std::collections::BTreeMap<String, Formula>) -> bool {
    // Must match trust-vcgen's `UNBOUNDED_ALLOC_ELEM_CEILING`. The large value is
    // what distinguishes the violation atom `Ge(count, CEILING)` from small-
    // threshold range/shift guards (`_1 >= 0`, `_2 < 64`).
    const ALLOC_CEILING: i128 = 1 << 28;
    if let Formula::Ge(lhs, rhs) | Formula::Gt(lhs, rhs) = f
        && let Formula::Int(c) = rhs.as_ref()
        && *c >= ALLOC_CEILING
        && let Some(cv) = eval_int_formula(lhs, env)
    {
        let holds = if matches!(f, Formula::Ge(..)) { cv >= *c } else { cv > *c };
        if holds {
            return true;
        }
    }
    f.children().into_iter().any(|child| alloc_violation_holds(child, env))
}

/// Benchmark comparing incremental session vs per-process verification.
///
/// Returns (incremental_total_ms, per_process_total_ms).
#[must_use]
pub fn benchmark_incremental_vs_fresh(
    solver_path: &str,
    vcs: &[VerificationCondition],
    common_formulas: &[(String, Formula)],
    timeout_ms: u64,
) -> (u64, u64) {
    // Incremental session.
    let mut session = IncrementalAYSession::with_solver_path(solver_path).with_timeout(timeout_ms);
    session.add_common_formulas(common_formulas);

    let start = Instant::now();
    for vc in vcs {
        session.verify_vc(vc);
    }
    let incremental_ms = start.elapsed().as_millis() as u64;

    // Per-process (fresh solver each time).
    let fresh_session =
        IncrementalAYSession::with_solver_path(solver_path).with_timeout(timeout_ms);

    let start = Instant::now();
    for vc in vcs {
        // Use per-process fallback directly.
        fresh_session.verify_per_process(vc);
    }
    let per_process_ms = start.elapsed().as_millis() as u64;

    (incremental_ms, per_process_ms)
}

/// Build the `Proved` verdict for a bare incremental-`ay` `unsat`.
///
/// This subprocess path does not request or validate a proof certificate, so the
/// honest assurance is [`AssuranceLevel::Unchecked`] ("solver said so, no
/// independent validation"), NEVER `Sound`. A buggy
/// solver-core UNSAT (e.g. the historical NIA sign bug) must not surface as a
/// complete proof: a boundary requiring `SmtBacked`/`Certified`
/// ([`VerificationResult::require_assurance`]) downgrades this `Unchecked`
/// `Proved` to `Unknown`. Locked by `bare_incremental_unsat_is_unchecked`.
fn proved_from_bare_unsat(time_ms: u64) -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay-incremental".into(),
        time_ms,
        strength: ProofStrength::smt_unsat_unvalidated(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

/// Preserve an already-received bare UNSAT while making persistent-context
/// cleanup fail-safe. Proof production is deliberately disabled, so no optional
/// query runs here. If `(pop 1)` cannot complete within the original query
/// deadline, discard the solver rather than letting cleanup availability change
/// the verdict or leave a desynchronized context for the next query.
fn finish_bare_unsat(
    state: &mut SessionState,
    time_ms: u64,
    deadline: Instant,
) -> VerificationResult {
    let proved = proved_from_bare_unsat(time_ms);
    let popped = state
        .process
        .as_mut()
        .is_some_and(|process| send_command_until(process, "(pop 1)", deadline).is_ok());
    if !popped {
        state.kill_process();
    }
    proved
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ScopedEnv {
        name: &'static str,
        previous: Option<std::ffi::OsString>,
    }

    impl ScopedEnv {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn remove(name: &'static str) -> Self {
            let previous = std::env::var_os(name);
            unsafe { std::env::remove_var(name) };
            Self { name, previous }
        }

        #[cfg(unix)]
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

    /// Hold the crate-wide process-environment lock while a solver-spawning
    /// test exercises the intentionally unconfigured admission lane. Without
    /// this guard, parallel coordinator tests can transiently install their
    /// private socket and make an unrelated solver test fail closed against the
    /// wrong authority. Environment restorations run before the lock field is
    /// dropped because struct fields are destroyed in declaration order.
    struct UnconfiguredMemoryAuthority {
        _socket: ScopedEnv,
        _disable: ScopedEnv,
        _token_file: ScopedEnv,
        _deadline: ScopedEnv,
        _solver_limit: ScopedEnv,
        _guard: std::sync::MutexGuard<'static, ()>,
    }

    fn unconfigured_memory_authority() -> UnconfiguredMemoryAuthority {
        let guard = crate::memory_jobserver::ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let socket = ScopedEnv::remove(crate::coordinator::SOCK_ENV);
        let disable = ScopedEnv::remove(crate::coordinator::DISABLE_ENV);
        let token_file = ScopedEnv::remove("TRUST_MEMORY_JOBSERVER");
        let deadline = ScopedEnv::remove("TRUST_MEMORY_JOBSERVER_DEADLINE_MS");
        let solver_limit = ScopedEnv::remove("TRUST_SOLVER_MEMORY_LIMIT_MB");
        UnconfiguredMemoryAuthority {
            _socket: socket,
            _disable: disable,
            _token_file: token_file,
            _deadline: deadline,
            _solver_limit: solver_limit,
            _guard: guard,
        }
    }

    #[cfg(unix)]
    struct TestTokenLane {
        directory: std::path::PathBuf,
        path: std::path::PathBuf,
    }

    #[cfg(unix)]
    impl TestTokenLane {
        fn new() -> Self {
            use std::os::unix::fs::PermissionsExt as _;

            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos();
            let directory = std::env::current_dir()
                .expect("test current directory")
                .join(format!(".trust-incremental-memory-test-{}-{nonce:x}", std::process::id()));
            std::fs::create_dir(&directory).expect("create private token fixture");
            std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))
                .expect("make token fixture private");
            let path = directory.join("tokens");
            crate::memory_jobserver::set_test_token_path(Some(path.clone()));
            Self { directory, path }
        }
    }

    #[cfg(unix)]
    impl Drop for TestTokenLane {
        fn drop(&mut self) {
            crate::memory_jobserver::set_test_token_path(None);
            let _ = std::fs::remove_file(&self.path);
            let mut lock = self.path.as_os_str().to_owned();
            lock.push(".lock");
            let _ = std::fs::remove_file(std::path::PathBuf::from(lock));
            let _ = std::fs::remove_dir(&self.directory);
        }
    }

    /// M-C3-prereq lock: the live `verify_incremental` unsat branch routes
    /// through `proved_from_bare_unsat`, which must stamp `Unchecked` (never the
    /// `Sound` of `smt_unsat()`). Mislabeling a bare, unvalidated solver UNSAT as
    /// `Sound` is the type-level root of solver-core false-PROVEs.
    #[test]
    fn bare_incremental_unsat_is_unchecked() {
        let result = proved_from_bare_unsat(7);
        match result {
            VerificationResult::Proved { strength, time_ms, .. } => {
                assert_eq!(time_ms, 7);
                assert_eq!(strength.assurance, AssuranceLevel::Unchecked);
                assert_ne!(
                    strength,
                    ProofStrength::smt_unsat(),
                    "bare incremental unsat must not be Sound-stamped"
                );
            }
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    #[test]
    fn bare_unsat_survives_expired_pop_deadline_and_resets_the_process() {
        let session = IncrementalAYSession::new();
        let (_tx, rx) = mpsc::channel();
        let mut state = session.state.lock().unwrap_or_else(|error| error.into_inner());
        state.process = Some(mock_proc(rx));
        state.base_initialized = true;
        let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();

        let result = finish_bare_unsat(&mut state, 9, expired);
        match result {
            VerificationResult::Proved { strength, time_ms, .. } => {
                assert_eq!(time_ms, 9);
                assert_eq!(strength.assurance, AssuranceLevel::Unchecked);
            }
            other => panic!("expected preserved bare UNSAT, got {other:?}"),
        }
        assert!(state.process.is_none(), "failed pop poisons and discards the solver");
        assert!(!state.base_initialized);
        assert!(!state.fallen_back, "cleanup failure cannot force per-process fallback");
    }

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    /// DIAGNOSTIC: the `|v| -v` closure negation VC — `_3 = (v == i64::MIN) ∧ _3` with
    /// `v` a FREE closure parameter. The violation (`v == MIN`) is merely POSSIBLE
    /// (depends on the free `v`), so it must NOT be classified forced/guaranteed.
    #[test]
    fn violation_is_forced_rejects_free_param_negation_min() {
        let viol_cond =
            Formula::Eq(Box::new(int_var("v")), Box::new(Formula::Int(i64::MIN as i128)));
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(bool_var("_3")), Box::new(viol_cond)),
            bool_var("_3"),
        ]);
        assert!(
            !violation_is_forced(&formula),
            "a free closure-parameter negation-at-MIN must NOT be a guaranteed violation"
        );
    }

    #[test]
    fn violation_is_forced_flags_constant_alloc() {
        // count == 1<<28 ; violation: count >= CEILING (== 1<<28). Forced true.
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(Formula::Int(ALLOC_CEILING)));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        assert!(
            violation_is_forced(&Formula::And(vec![count_def, viol])),
            "a constant 1<<28 allocation must be a forced/guaranteed violation"
        );
    }

    #[test]
    fn alloc_over_ceiling_forced_catches_alloc_behind_unpinned_shift_guard() {
        // The REAL nn-OOM alloc VC shape that `violation_is_forced` alone CANNOT
        // fold: the constant over-budget count is conjoined with a reaching shift-
        // panic-freedom guard `shift_amt < 64` whose amount vcgen leaves UNPINNED.
        // `violation_is_forced` evaluates the whole conjunction, so the free
        // `shift_amt` makes it unknown and the OOM would (wrongly) stay a warning —
        // this is exactly why `origin/main`'s violation_is_forced-only gate misses
        // it. `alloc_over_ceiling_forced` checks the VIOLATION ATOM only: the count
        // folds to 1<<28 >= CEILING regardless of the guard, so it is guaranteed.
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(Formula::Int(ALLOC_CEILING)));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        let guard = Formula::Lt(Box::new(int_var("shift_amt")), Box::new(Formula::Int(64)));
        let real_vc = Formula::And(vec![count_def, guard, viol]);
        assert!(
            !violation_is_forced(&real_vc),
            "whole-conjunction folding cannot see past the unpinned shift guard"
        );
        assert!(
            alloc_over_ceiling_forced(&real_vc),
            "the violation-atom check must catch the constant over-budget count \
             regardless of the unpinned reaching guard (the nn OOM case)"
        );
    }

    #[test]
    fn alloc_over_ceiling_forced_rejects_input_dependent_count_behind_guard() {
        // Same guarded shape, but count == a + b (FREE inputs): the violation atom
        // does NOT fold to a constant >= ceiling, so this stays a (correct) warning
        // — `alloc_over_ceiling_forced` must not over-fire on input-dependent allocs.
        let count = int_var("count");
        let sum = Formula::Add(Box::new(int_var("a")), Box::new(int_var("b")));
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(sum));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        let guard = Formula::Lt(Box::new(int_var("shift_amt")), Box::new(Formula::Int(64)));
        let real_vc = Formula::And(vec![count_def, guard, viol]);
        assert!(
            !alloc_over_ceiling_forced(&real_vc),
            "an input-dependent count must NOT be a guaranteed over-budget violation"
        );
    }

    #[test]
    fn violation_is_forced_flags_constant_alloc_through_bool_temp() {
        // The real VC shape: count pinned, a BOOL temp `flag == (count >= CEILING)`,
        // and the formula asserts `flag`. Needs bool-equality propagation to fold.
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(Formula::Int(ALLOC_CEILING)));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        let flag = bool_var("flag");
        let flag_def = Formula::Eq(Box::new(flag.clone()), Box::new(viol));
        assert!(
            violation_is_forced(&Formula::And(vec![count_def, flag_def, flag])),
            "a constant alloc flowing through a bool block-def temp must fold to forced"
        );
    }

    #[test]
    fn violation_is_forced_rejects_input_dependent_overflow() {
        // a + b > u32::MAX with a, b FREE inputs -> merely POSSIBLE, not guaranteed.
        let viol = Formula::Gt(
            Box::new(Formula::Add(Box::new(int_var("a")), Box::new(int_var("b")))),
            Box::new(Formula::Int(i128::from(u32::MAX))),
        );
        assert!(
            !violation_is_forced(&Formula::And(vec![viol])),
            "input-dependent overflow must NOT be treated as a guaranteed violation"
        );
    }

    #[test]
    fn violation_is_forced_rejects_small_constant_alloc() {
        // count == 16 ; 16 >= CEILING is false -> not a violation -> not forced.
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(Formula::Int(16)));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        assert!(
            !violation_is_forced(&Formula::And(vec![count_def, viol])),
            "a small constant allocation is bounded and must not be flagged"
        );
    }

    #[test]
    fn violation_is_forced_flags_bv_encoded_constant_count() {
        // count == BvToInt(BvShl(IntToBv(1), IntToBv(28))) == 1<<28 (the shift kept
        // as a bit-vector round-trip rather than const-folded). Must still fold.
        let bv1 = Formula::IntToBv(Box::new(Formula::Int(1)), 64);
        let bv28 = Formula::IntToBv(Box::new(Formula::Int(28)), 64);
        let count_val = Formula::BvToInt(
            Box::new(Formula::BvShl(Box::new(bv1), Box::new(bv28), 64)),
            64,
            false,
        );
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(count_val));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        assert!(
            violation_is_forced(&Formula::And(vec![count_def, viol])),
            "a constant count encoded via a BV shift round-trip must fold to forced"
        );
    }

    #[test]
    fn violation_is_forced_rejects_symbolically_bounded_alloc() {
        // count == n, with only `n <= 100` known (a symbolic precondition, NOT an
        // equality pin). n is free -> the violation cannot fold -> not guaranteed.
        let n = int_var("n");
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(n.clone()));
        let bound = Formula::Le(Box::new(n), Box::new(Formula::Int(100)));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        assert!(
            !violation_is_forced(&Formula::And(vec![count_def, bound, viol])),
            "a symbolically-bounded allocation must NOT be treated as guaranteed"
        );
    }

    #[test]
    fn modeling_gap_failclose_flags_bare_true_literal() {
        // A bare `Bool(true)` is the vcgen modeling-gap fail-close marker (the
        // `Index<Range>` body with an unresolved receiver length / an untraceable
        // range aggregate). It IS `violation_is_forced` (it folds to true), which is
        // exactly why the guaranteed-violation escalation needs a second
        // discriminator to keep it out.
        assert!(violation_is_forced(&Formula::Bool(true)));
        assert!(
            violation_is_modeling_gap_failclose(&Formula::Bool(true)),
            "a bare `true` literal is a modeling-gap fail-close, not a program-forced violation"
        );
    }

    #[test]
    fn modeling_gap_failclose_rejects_genuine_ground_violation() {
        // A genuine guaranteed violation folds through REAL atoms (`Ge(100, 64)` —
        // a constant out-of-bounds index). It must NOT be classified as a
        // modeling-gap fail-close, so it still escalates.
        let ground_oob = Formula::Ge(Box::new(Formula::Int(100)), Box::new(Formula::Int(64)));
        assert!(violation_is_forced(&ground_oob));
        assert!(
            !violation_is_modeling_gap_failclose(&ground_oob),
            "a real ground constant-OOB violation must stay escalatable (not a modeling gap)"
        );
        // The constant-allocation ground violation likewise stays escalatable.
        let ground_alloc = Formula::Ge(
            Box::new(Formula::Int(ALLOC_CEILING)),
            Box::new(Formula::Int(ALLOC_CEILING)),
        );
        assert!(!violation_is_modeling_gap_failclose(&ground_alloc));
        // And so does the real constant-alloc VC shape (`count == 1<<28` pinned by a
        // block-def, violation `count >= CEILING`): it is a conjunction over modeled
        // atoms, not a bare literal.
        let count = int_var("count");
        let count_def = Formula::Eq(Box::new(count.clone()), Box::new(Formula::Int(ALLOC_CEILING)));
        let viol = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        let real_vc = Formula::And(vec![count_def, viol]);
        assert!(violation_is_forced(&real_vc));
        assert!(
            !violation_is_modeling_gap_failclose(&real_vc),
            "a modeled conjunction that folds to true is not a bare-literal modeling gap"
        );
    }

    #[test]
    fn modeling_gap_failclose_rejects_bool_false() {
        // `Bool(false)` (a provably-safe / vacuously-UNSAT obligation) is not a
        // fail-close marker — the classifier must not fire on it.
        assert!(!violation_is_modeling_gap_failclose(&Formula::Bool(false)));
    }

    fn u32_mul_overflow_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Mul,
                operand_tys: (Ty::u32(), Ty::u32()),
            },
            function: "mul".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    // -- Session construction tests --

    #[test]
    fn test_session_default_config() {
        let session = IncrementalAYSession::new();
        assert_eq!(session.solver_path, "ay");
        // No redundant `-in`: it is an alias of `--incremental` in the pinned
        // ay, so passing both makes ay reject the invocation. `--incremental`
        // alone drives the stdin push/pop protocol.
        assert_eq!(
            session.solver_args,
            vec!["--z3-mode".to_string(), "-smt2".to_string(), "--incremental".to_string(),]
        );
        assert_eq!(session.query_timeout_ms, DEFAULT_QUERY_TIMEOUT_MS);
        assert!(session.common_assertions.is_empty());
        assert!(session.logic.is_none());
        assert!(!session.stats().permanently_fallen_back);
    }

    #[test]
    fn test_session_builder() {
        let session = IncrementalAYSession::with_solver_path("/opt/ay")
            .with_timeout(60_000)
            .with_logic("QF_LIA");

        assert_eq!(session.solver_path, "/opt/ay");
        assert_eq!(session.query_timeout_ms, 60_000);
        assert_eq!(session.logic.as_deref(), Some("QF_LIA"));
    }

    #[test]
    fn test_session_default_impl() {
        let session = IncrementalAYSession::default();
        assert_eq!(session.solver_path, "ay");
    }

    #[test]
    fn test_memory_limit_propagates_into_spawn_args() {
        // The per-job ceiling must reach the spawned `ay` as `--memory <mb>` so
        // the solver self-limits (degrades to Unknown) instead of OOM-killing the
        // host. The stored solver_args are unchanged; only spawn_args() carries it.
        let session = IncrementalAYSession::new().with_memory_limit_mb(4096);
        let args = session.solver_memory_plan().expect("memory plan").args;
        let pos = args.iter().position(|a| a == "--memory").expect("--memory must be present");
        assert_eq!(args.get(pos + 1).map(String::as_str), Some("4096"));
        // The stored args (used for equality tests elsewhere) are not mutated.
        assert!(!session.solver_args.iter().any(|a| a == "--memory"));
    }

    #[cfg(unix)]
    #[test]
    fn active_reservation_exactly_matches_the_enforced_memory_argument() {
        let _env = crate::memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _socket = ScopedEnv::remove(crate::coordinator::SOCK_ENV);
        let _disable = ScopedEnv::remove(crate::coordinator::DISABLE_ENV);
        let _lane = TestTokenLane::new();
        let session = IncrementalAYSession::new().with_memory_limit_mb(16);
        let plan = session.solver_memory_plan().expect("memory plan");
        let args = &plan.args;
        let position = args.iter().position(|arg| arg == "--memory").expect("memory flag");
        let enforced_mb = args[position + 1].parse::<u64>().expect("numeric memory ceiling");

        let reservation = session.acquire_reservation(&plan).expect("active file admission");
        assert!(reservation.is_active());
        assert_eq!(reservation.bytes(), enforced_mb * 1024 * 1024);
        drop(reservation);
    }

    #[test]
    fn unrepresentable_memory_ceiling_fails_before_reservation_or_spawn() {
        let session = IncrementalAYSession::new().with_memory_limit_mb(u64::MAX);
        let error = session
            .solver_memory_plan()
            .err()
            .expect("an inexact MB-to-byte reservation must fail closed");
        assert!(error.contains("not representable as an exact reservation"));
    }

    #[cfg(unix)]
    #[test]
    fn pre_spawn_admission_failure_is_not_retried_or_counted_as_solver_failure() {
        let _env = crate::memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _socket = ScopedEnv::set(crate::coordinator::SOCK_ENV, "");
        let _disable = ScopedEnv::remove(crate::coordinator::DISABLE_ENV);
        let session = IncrementalAYSession::new().with_memory_limit_mb(1);
        // Keep a nonlinear term in the VC: the public path would ordinarily
        // attempt the sound relaxation after an Unknown. Admission failure must
        // bypass that second solve as well as the one-shot fallback.
        let formula = Formula::Eq(
            Box::new(Formula::Rem(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(0)),
        );

        let result = session.verify_vc(&make_vc(formula));
        let VerificationResult::Unknown { reason, .. } = result else {
            panic!("pre-spawn admission failure must remain Unknown");
        };
        assert!(is_pre_spawn_admission_error(&reason));
        assert!(reason.contains("configured with an empty path"));

        let state = session.state.lock().unwrap_or_else(|error| error.into_inner());
        assert!(state.process.is_none(), "admission failure cannot spawn a solver");
        assert_eq!(state.consecutive_failures, 0);
        assert!(!state.fallen_back);
        assert_eq!(state.stats.total_queries, 1, "nonlinear relaxation must not retry admission");
        assert_eq!(state.stats.restarts, 0);
        assert_eq!(state.stats.fallback_queries, 0);
    }

    #[cfg(unix)]
    #[test]
    fn memory_plan_snapshot_cannot_split_after_environment_mutation() {
        let _env = crate::memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _limit = ScopedEnv::set("TRUST_SOLVER_MEMORY_LIMIT_MB", "8");
        let session = IncrementalAYSession::new();
        let plan = session.solver_memory_plan().expect("snapshot eight-MiB plan");
        let _mutated = ScopedEnv::set("TRUST_SOLVER_MEMORY_LIMIT_MB", "8192");

        assert_eq!(plan.limit_mb, Some(8));
        assert_eq!(plan.reservation_bytes, 8 * 1024 * 1024);
        let position = plan.args.iter().position(|argument| argument == "--memory").unwrap();
        assert_eq!(plan.args.get(position + 1).map(String::as_str), Some("8"));
    }

    #[test]
    fn test_default_memory_ceiling_applied() {
        // Serialize against tests that set TRUST_MEMORY_JOBSERVER (process-global
        // env); under the lock no jobserver is active.
        let _env = crate::memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // A spawned ay is never unbounded by default: with no explicit ceiling
        // and no jobserver, the budget-derived per-job ceiling (70% RAM /
        // parallelism, 1 GiB floor) is applied — the pre-2026-07 "drop-in"
        // no-ceiling behavior left the plain-cargo lane's solver unbounded
        // (the aterm-lz4 / trustc 300 GB incident class). Unbounded now only
        // happens when RAM is undetectable.
        let session = IncrementalAYSession::new();
        let derived = crate::memory_jobserver::default_per_job_limit_mb();
        let plan = session.solver_memory_plan().expect("default memory plan");
        let has_flag = plan.args.iter().any(|a| a == "--memory");
        assert_eq!(has_flag, derived.is_some());
        // A zero ceiling clears the explicit setting (env/derived may still apply).
        let zeroed = IncrementalAYSession::new().with_memory_limit_mb(0);
        assert!(zeroed.solver_memory_limit_mb.is_none());
    }

    #[test]
    fn test_env_memory_limit_honored() {
        // TRUST_SOLVER_MEMORY_LIMIT_MB is documented as the solver ceiling knob
        // on targo's router; the in-compiler session must honor it too. Uses the
        // env lock to avoid races with jobserver env tests.
        let _env = crate::memory_jobserver::ENV_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _limit = ScopedEnv::set("TRUST_SOLVER_MEMORY_LIMIT_MB", "3072");
        let session = IncrementalAYSession::new();
        let args = session.solver_memory_plan().expect("environment memory plan").args;
        let pos = args.iter().position(|a| a == "--memory").expect("--memory must be present");
        assert_eq!(args.get(pos + 1).map(String::as_str), Some("3072"));
        // 0 clears the override; it cannot request an unbounded solver or
        // decouple the enforced flag from aggregate admission.
        let _cleared = ScopedEnv::set("TRUST_SOLVER_MEMORY_LIMIT_MB", "0");
        let cleared = IncrementalAYSession::new();
        let derived = crate::memory_jobserver::default_per_job_limit_mb();
        let args = cleared.solver_memory_plan().expect("cleared memory plan").args;
        let actual = args
            .iter()
            .position(|arg| arg == "--memory")
            .and_then(|position| args.get(position + 1))
            .and_then(|value| value.parse::<u64>().ok());
        assert_eq!(actual, derived);
    }

    // -- Common assertion tests --

    #[test]
    fn test_common_assertion_from_formula() {
        let formula = Formula::Ge(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let assertion = CommonAssertion::from_formula("x_nonneg", &formula);

        assert_eq!(assertion.label, "x_nonneg");
        assert!(!assertion.commands.is_empty());

        // Should contain the declaration and assertion.
        let joined = assertion.commands.join("\n");
        assert!(joined.contains("declare"), "should contain variable declaration");
        assert!(joined.contains("(assert"), "should contain assertion");
    }

    #[test]
    fn test_common_assertion_from_commands() {
        let commands = vec!["(declare-fun x () Int)".to_string(), "(assert (>= x 0))".to_string()];
        let assertion = CommonAssertion::from_commands("range", commands.clone());

        assert_eq!(assertion.label, "range");
        assert_eq!(assertion.commands, commands);
    }

    #[test]
    fn test_add_common_assertion_updates_stats() {
        let mut session = IncrementalAYSession::new();
        assert_eq!(session.stats().common_assertions, 0);

        session.add_common_assertion(CommonAssertion::from_commands(
            "test",
            vec!["(assert true)".to_string()],
        ));
        assert_eq!(session.stats().common_assertions, 1);

        session.add_common_assertion(CommonAssertion::from_commands(
            "test2",
            vec!["(assert false)".to_string()],
        ));
        assert_eq!(session.stats().common_assertions, 2);
    }

    #[test]
    fn test_add_common_formulas() {
        let mut session = IncrementalAYSession::new();
        let formulas = vec![
            (
                "x_bound".to_string(),
                Formula::Le(Box::new(int_var("x")), Box::new(Formula::Int(100))),
            ),
            ("y_bound".to_string(), Formula::Ge(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        session.add_common_formulas(&formulas);
        assert_eq!(session.stats().common_assertions, 2);
    }

    // -- Extract common declarations tests --

    #[test]
    fn test_extract_common_declarations_shared_vars() {
        let mut session = IncrementalAYSession::new();

        let vcs = vec![
            make_vc(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(100)))),
            make_vc(Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(42)))),
        ];

        session.extract_common_declarations(&vcs);

        // "x" appears in 2 VCs, so it should be promoted.
        // "y" appears in only 1 VC, so it should not be promoted.
        assert_eq!(session.stats().common_assertions, 1);
        let assertion = &session.common_assertions[0];
        assert_eq!(assertion.label, "shared-variable-declarations");

        let commands_str = assertion.commands.join(" ");
        assert!(commands_str.contains("x"), "should contain shared var x");
    }

    #[test]
    fn test_extract_common_declarations_no_shared() {
        let mut session = IncrementalAYSession::new();

        let vcs = vec![
            make_vc(Formula::Gt(Box::new(int_var("a")), Box::new(Formula::Int(0)))),
            make_vc(Formula::Lt(Box::new(int_var("b")), Box::new(Formula::Int(100)))),
        ];

        session.extract_common_declarations(&vcs);

        // No variables appear in 2+ VCs.
        assert_eq!(session.stats().common_assertions, 0);
    }

    // -- extract_declared_name tests --

    #[test]
    fn test_extract_var_name_declare_fun() {
        assert_eq!(extract_declared_name("(declare-fun x () Int)"), Some("x".to_string()));
        assert_eq!(
            extract_declared_name("(declare-fun my_var () Bool)"),
            Some("my_var".to_string())
        );
    }

    #[test]
    fn test_extract_var_name_declare_const() {
        assert_eq!(extract_declared_name("(declare-const x Int)"), Some("x".to_string()));
    }

    #[test]
    fn test_extract_var_name_other() {
        assert_eq!(extract_declared_name("(assert (> x 0))"), None);
        assert_eq!(extract_declared_name("(set-logic QF_LIA)"), None);
        assert_eq!(extract_declared_name("(push 1)"), None);
    }

    /// Trust: Lever A's datatype preamble introduces two MORE declaration
    /// shapes. They bind a name in the same solver namespace as a variable, so
    /// the same identity extractor must see them — otherwise the per-VC push
    /// scope re-emits the base scope's `(declare-datatype …)` and errors the
    /// session.
    #[test]
    fn extract_declared_name_reads_sort_and_datatype_declarations() {
        assert_eq!(extract_declared_name("(declare-sort Expr 0)"), Some("Expr".to_string()));
        assert_eq!(
            extract_declared_name(
                "(declare-datatype Expr ((Const (c (_ BitVec 32))) (App (f Expr) (x Expr))))"
            ),
            Some("Expr".to_string())
        );
        // The plural multi-sort form is NOT emitted by `emit_declarations` and
        // its first token is a sort LIST, not a name — it must not be misread.
        assert_eq!(extract_declared_name("(declare-datatypes ((Expr 0)) (((Leaf))))"), None);
    }

    #[test]
    fn declares_sort_separates_sort_declarations_from_value_declarations() {
        assert!(declares_sort("(declare-sort Expr 0)"));
        assert!(declares_sort("(declare-datatype Expr ((Leaf)))"));
        assert!(!declares_sort("(declare-fun e () Expr)"));
        assert!(!declares_sort("(declare-const e Expr)"));
        assert!(!declares_sort("(assert (= e e))"));
    }

    /// AY's element-count ceiling (mirrors `UNBOUNDED_ALLOC_ELEM_CEILING`).
    const ALLOC_CEILING: i128 = 1 << 28;

    fn unbounded_alloc_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: "Vec::from_elem".into(),
                count: "s * s * 12".into(),
                detail: "test".into(),
            },
            function: "flash_attn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    // -- O(S^2) UnboundedAllocation witness tests --

    /// The nn flash-attn shape: `count == s * s * 12 AND count >= 1<<28`. This is
    /// QF_NIA (ay returns `unknown`); the witness must DECIDE it `Failed` with a
    /// concrete `s` whose `s * s * 12` reaches the ceiling.
    #[test]
    fn test_unbounded_alloc_nonlinear_is_decided_failed() {
        let s = int_var("s");
        let count = int_var("count");
        // count == s * s * 12
        let count_def = Formula::Eq(
            Box::new(count.clone()),
            Box::new(Formula::Mul(
                Box::new(Formula::Mul(Box::new(s.clone()), Box::new(s))),
                Box::new(Formula::Int(12)),
            )),
        );
        // failure: count >= CEILING
        let ceiling = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        let formula = Formula::And(vec![count_def, ceiling]);

        let result = mul_counterexample(&unbounded_alloc_vc(formula));
        let Some(VerificationResult::Failed { solver, counterexample: Some(cex), .. }) = result
        else {
            panic!("O(S^2) UnboundedAllocation must be DECIDED Failed, not left unknown");
        };
        assert_eq!(solver, "ay-incremental-witness");
        // The witness assigns concrete s, and s*s*12 must actually reach the ceiling.
        let s_val = cex
            .assignments
            .iter()
            .find(|(name, _)| name == "s")
            .map(|(_, v)| match v {
                CounterexampleValue::Uint(n) => *n as i128,
                CounterexampleValue::Int(n) => *n,
                _ => panic!("unexpected witness value kind"),
            })
            .expect("witness must bind s");
        assert!(
            s_val * s_val * 12 >= ALLOC_CEILING,
            "witness s={s_val} must satisfy s*s*12 >= {ALLOC_CEILING}"
        );
    }

    /// A SAFE allocation guarded by `s <= 1000` can never reach the ceiling
    /// (`1000*1000*12 = 12_000_000 < 1<<28`), so the witness must NOT fire — the
    /// guard makes every candidate model evaluate to `false`.
    #[test]
    fn test_unbounded_alloc_guarded_is_not_spuriously_failed() {
        let s = int_var("s");
        let count = int_var("count");
        let count_def = Formula::Eq(
            Box::new(count.clone()),
            Box::new(Formula::Mul(
                Box::new(Formula::Mul(Box::new(s.clone()), Box::new(s.clone()))),
                Box::new(Formula::Int(12)),
            )),
        );
        let ceiling = Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING)));
        // dominating precondition: s <= 1000.
        let guard = Formula::Le(Box::new(s), Box::new(Formula::Int(1000)));
        let formula = Formula::And(vec![guard, count_def, ceiling]);

        assert!(
            mul_counterexample(&unbounded_alloc_vc(formula)).is_none(),
            "a guarded sub-ceiling allocation must not be spuriously failed"
        );
    }

    /// An UnboundedAllocation whose formula has NO symbolic mul (linear count)
    /// must be left untouched (returns `None`) — the witness only handles the
    /// nonlinear gap and must not steal linear obligations from the solver.
    #[test]
    fn test_unbounded_alloc_linear_count_untouched() {
        let n = int_var("n");
        // count == n (linear); failure n >= CEILING. No Mul atom.
        let formula = Formula::Ge(Box::new(n), Box::new(Formula::Int(ALLOC_CEILING)));
        assert!(
            mul_counterexample(&unbounded_alloc_vc(formula)).is_none(),
            "a linear allocation count has no symbolic mul; leave it to the solver"
        );
    }

    #[test]
    fn test_isqrt_i128_floor() {
        assert_eq!(isqrt_i128(0), 0);
        assert_eq!(isqrt_i128(1), 1);
        assert_eq!(isqrt_i128(15), 3);
        assert_eq!(isqrt_i128(16), 4);
        assert_eq!(isqrt_i128(ALLOC_CEILING), 16_384); // (1<<14)^2 == 1<<28.
    }

    #[test]
    fn test_mul_overflow_witness_reports_valid_counterexample() {
        let a = int_var("a");
        let b = int_var("b");
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a.clone()), Box::new(Formula::Int(u32::MAX.into()))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(b.clone())),
            Formula::Le(Box::new(b.clone()), Box::new(Formula::Int(u32::MAX.into()))),
            Formula::Gt(
                Box::new(Formula::Mul(Box::new(a), Box::new(b))),
                Box::new(Formula::Int(u32::MAX.into())),
            ),
        ]);

        let result = mul_counterexample(&u32_mul_overflow_vc(formula));
        let Some(VerificationResult::Failed { solver, counterexample: Some(cex), .. }) = result
        else {
            panic!("expected witness-backed failed multiplication overflow result");
        };
        assert_eq!(solver, "ay-incremental-witness");
        assert_eq!(cex.assignments.len(), 2);
        assert!(
            cex.assignments
                .iter()
                .all(|(_, value)| matches!(value, CounterexampleValue::Uint(65_536)))
        );
    }

    #[test]
    fn test_mul_overflow_witness_respects_path_guards() {
        let a = int_var("a");
        let b = int_var("b");
        let formula = Formula::And(vec![
            Formula::Le(Box::new(a.clone()), Box::new(Formula::Int(65_535))),
            Formula::Le(Box::new(b.clone()), Box::new(Formula::Int(65_535))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a.clone()), Box::new(Formula::Int(u32::MAX.into()))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(b.clone())),
            Formula::Le(Box::new(b.clone()), Box::new(Formula::Int(u32::MAX.into()))),
            Formula::Gt(
                Box::new(Formula::Mul(Box::new(a), Box::new(b))),
                Box::new(Formula::Int(u32::MAX.into())),
            ),
        ]);

        assert!(mul_counterexample(&u32_mul_overflow_vc(formula)).is_none());
    }

    // -- VerificationBackend trait tests --

    #[test]
    fn test_backend_name() {
        let session = IncrementalAYSession::new();
        assert_eq!(session.name(), "ay-incremental");
    }

    #[test]
    fn test_backend_role() {
        let session = IncrementalAYSession::new();
        assert_eq!(session.role(), BackendRole::SmtSolver);
    }

    #[test]
    fn test_backend_can_handle_l0() {
        let session = IncrementalAYSession::new();
        let vc = make_vc(Formula::Bool(false));
        assert!(session.can_handle(&vc));
    }

    #[test]
    fn test_backend_can_handle_l1() {
        let session = IncrementalAYSession::new();
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(session.can_handle(&vc));
    }

    #[test]
    fn test_backend_cannot_handle_l2() {
        let session = IncrementalAYSession::new();
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!session.can_handle(&vc));
    }

    // -- Fallback behavior tests --

    #[test]
    fn test_session_falls_back_on_bad_solver_path() {
        let _memory_authority = unconfigured_memory_authority();
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        let result = session.verify_vc(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));

        let stats = session.stats();
        assert_eq!(stats.total_queries, 1);
        assert_eq!(stats.restarts, 1);
    }

    #[test]
    fn test_session_permanent_fallback() {
        let _memory_authority = unconfigured_memory_authority();
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        for _ in 0..MAX_CONSECUTIVE_FAILURES {
            let _ = session.verify_vc(&vc);
        }

        let stats = session.stats();
        assert!(
            stats.permanently_fallen_back,
            "should fall back after {MAX_CONSECUTIVE_FAILURES} failures"
        );
    }

    #[test]
    fn test_session_stats_after_failures() {
        let _memory_authority = unconfigured_memory_authority();
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        // Trigger MAX_CONSECUTIVE_FAILURES + 1 queries.
        for _ in 0..=MAX_CONSECUTIVE_FAILURES {
            let _ = session.verify_vc(&vc);
        }

        let stats = session.stats();
        assert_eq!(stats.total_queries, MAX_CONSECUTIVE_FAILURES as u64 + 1);
        assert_eq!(stats.restarts, MAX_CONSECUTIVE_FAILURES as u64);
        assert!(stats.permanently_fallen_back);
        // Queries 1..MAX each fail incremental and fall back to per-process (3 fallbacks).
        // Query MAX+1 hits permanent fallback directly (1 more fallback).
        assert_eq!(stats.fallback_queries, MAX_CONSECUTIVE_FAILURES as u64 + 1);
    }

    // -- Batch verification tests --

    #[test]
    fn test_verify_batch_preserves_order() {
        let _memory_authority = unconfigured_memory_authority();
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_xyz");

        let vcs = vec![
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        let results = session.verify_batch(&vcs);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].0.function, "test_fn");
        assert_eq!(results[1].0.function, "test_fn");
    }

    #[test]
    fn test_verify_batch_empty() {
        let session = IncrementalAYSession::new();
        let results = session.verify_batch(&[]);
        assert!(results.is_empty());
    }

    // -- Push/pop script structure tests --

    #[test]
    fn test_incremental_protocol_structure() {
        // Verify the SMT-LIB2 command sequence follows the push/pop protocol.
        let vc = make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10))));

        let logic = smt2_export::detect_logic(&vc.formula);
        let decls = smt2_export::emit_declarations(&vc.formula);
        let assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));

        // Build expected command sequence.
        let commands = [
            "(push 1)".to_string(),
            decls.join("\n"),
            assertion,
            "(check-sat)".to_string(),
            "(pop 1)".to_string(),
        ];

        assert_eq!(commands[0], "(push 1)");
        assert!(commands[1].contains("(declare-fun x () Int)"));
        assert!(commands[2].contains("(assert (< x 10))"));
        assert_eq!(commands[3], "(check-sat)");
        assert_eq!(commands[4], "(pop 1)");

        // Logic should be QF_LIA for integer comparisons.
        assert_eq!(logic, "QF_LIA");
    }

    #[test]
    fn test_multiple_vcs_separate_scopes() {
        let vcs = vec![
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        let mut push_count = 0;
        let mut pop_count = 0;

        for vc in &vcs {
            push_count += 1; // (push 1)
            let _decls = smt2_export::emit_declarations(&vc.formula);
            let _assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));
            // (check-sat) + result handling
            pop_count += 1; // (pop 1)
        }

        assert_eq!(push_count, 2);
        assert_eq!(pop_count, 2);
    }

    // -- Benchmark function signature tests --

    #[test]
    fn test_benchmark_with_empty_vcs() {
        let (incr_ms, pp_ms) = benchmark_incremental_vs_fresh("nonexistent_xyz", &[], &[], 1000);
        assert!(incr_ms < 100);
        assert!(pp_ms < 100);
    }

    // -- Stats tests --

    #[test]
    fn test_initial_stats() {
        let session = IncrementalAYSession::new();
        let stats = session.stats();
        assert_eq!(stats.total_queries, 0);
        assert_eq!(stats.incremental_queries, 0);
        assert_eq!(stats.fallback_queries, 0);
        assert_eq!(stats.restarts, 0);
        assert!(!stats.permanently_fallen_back);
        assert_eq!(stats.common_assertions, 0);
    }

    // -- Timeout enforcement test --

    #[test]
    fn test_remaining_timeout_returns_minimum() {
        let start = Instant::now();
        std::thread::sleep(Duration::from_millis(5));
        let remaining = remaining_timeout(Duration::from_millis(1), start);
        assert_eq!(remaining, Duration::from_millis(1));
    }

    #[test]
    fn test_remaining_timeout_normal() {
        let start = Instant::now();
        let remaining = remaining_timeout(Duration::from_secs(10), start);
        // Should be close to 10 seconds.
        assert!(remaining.as_secs() >= 9);
    }

    #[cfg(unix)]
    #[test]
    fn persistent_write_to_non_reader_stops_at_absolute_deadline() {
        let mut child = Command::new("/bin/sleep")
            .arg("30")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn non-reading solver fixture");
        let stdin = child.stdin.take().expect("capture non-reader stdin");
        let (_tx, rx) = mpsc::channel();
        let mut proc = SolverProcess {
            child,
            group_isolated: false,
            stdin,
            line_rx: rx,
            _reservation: crate::coordinator::Reservation::inert(),
        };
        let command = "x".repeat(4 * 1024 * 1024);
        let start = Instant::now();
        let deadline = start.checked_add(Duration::from_millis(50)).unwrap_or(start);
        let error = send_command_until(&mut proc, &command, deadline)
            .expect_err("a non-reading solver cannot block stdin forever");
        assert!(error.contains("deadline"), "bounded write diagnostic: {error}");
        assert!(start.elapsed() < Duration::from_secs(1));
    }

    #[cfg(unix)]
    #[test]
    fn killing_non_reader_breaks_and_joins_one_shot_writer() {
        let mut command = Command::new("/bin/sleep");
        command.arg("30").stdin(Stdio::piped()).stdout(Stdio::null()).stderr(Stdio::null());
        isolate_solver_process_group(&mut command);
        let mut child = command.spawn().expect("spawn one-shot non-reader");
        let stdin = child.stdin.take().expect("capture one-shot stdin");
        let mut child =
            ReservedSolverChild::new(child, crate::coordinator::Reservation::inert(), true);
        let writer = spawn_solver_writer(stdin, vec![b'x'; 4 * 1024 * 1024])
            .expect("spawn bounded-lifecycle writer");
        std::thread::sleep(Duration::from_millis(50));
        assert!(!writer.is_finished(), "non-reader fixture should fill its stdin pipe");

        let start = Instant::now();
        child.terminate_and_reap();
        let error = join_solver_writer(writer)
            .expect_err("killing the non-reader breaks its blocked writer");
        assert!(error.contains("solver stdin"));
        assert!(start.elapsed() < Duration::from_secs(1));
    }

    #[cfg(unix)]
    #[test]
    fn reserved_child_drop_kills_background_process_group_before_return() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static NEXT: AtomicU64 = AtomicU64::new(0);
        let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
        let marker = std::env::temp_dir()
            .join(format!("trust-ay-timeout-marker-{}-{sequence}", std::process::id()));
        let _ = std::fs::remove_file(&marker);

        let mut command = Command::new("/bin/sh");
        command
            .arg("-c")
            .arg("(sleep 0.4; printf leaked > \"$1\") & wait")
            .arg("trust-ay-timeout-test")
            .arg(&marker)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        isolate_solver_process_group(&mut command);
        let child = command.spawn().expect("spawn solver process-group fixture");
        let guarded =
            ReservedSolverChild::new(child, crate::coordinator::Reservation::inert(), true);
        // The wrapper shell and its delayed background writer are both live.
        // Dropping the reservation guard must synchronously kill/reap the group.
        std::thread::sleep(Duration::from_millis(50));
        drop(guarded);
        std::thread::sleep(Duration::from_millis(500));
        assert!(
            !marker.exists(),
            "a timeout/error return left a background solver descendant running"
        );
    }

    // -- I/O helper tests (matching incremental_smtlib_backend pattern) --

    #[test]
    fn test_read_response_line_timeout() {
        let (_tx, rx) = mpsc::channel::<Result<String, String>>();
        let mut proc = SolverProcess {
            child: Command::new("true").spawn().expect("spawn true"),
            group_isolated: false,
            stdin: Command::new("true")
                .stdin(Stdio::piped())
                .spawn()
                .expect("spawn true for stdin")
                .stdin
                .take()
                .expect("stdin"),
            line_rx: rx,
            _reservation: crate::coordinator::Reservation::inert(),
        };

        let start = Instant::now();
        let result = read_response_line(&mut proc, Duration::from_millis(100));
        let elapsed = start.elapsed();

        assert!(result.is_err(), "should timeout");
        assert!(result.unwrap_err().contains("timeout"), "error should mention timeout");
        assert!(elapsed.as_millis() < 2000, "should timeout quickly, took {elapsed:?}");

        drop(proc);
    }

    #[test]
    fn test_read_response_line_receives_data() {
        let (tx, rx) = mpsc::channel();
        tx.send(Ok("success\n".to_string())).unwrap();

        let mut proc = SolverProcess {
            child: Command::new("true").spawn().expect("spawn true"),
            group_isolated: false,
            stdin: Command::new("true")
                .stdin(Stdio::piped())
                .spawn()
                .expect("spawn true for stdin")
                .stdin
                .take()
                .expect("stdin"),
            line_rx: rx,
            _reservation: crate::coordinator::Reservation::inert(),
        };

        let result = read_response_line(&mut proc, Duration::from_secs(1));
        assert!(result.is_ok());
        assert_eq!(result.unwrap().trim(), "success");

        drop(proc);
    }

    #[test]
    fn ready_comment_flood_cannot_extend_the_absolute_response_deadline() {
        let (tx, rx) = mpsc::sync_channel(1);
        let producer =
            std::thread::spawn(
                move || {
                    while tx.send(Ok("c endless-banner\n".to_string())).is_ok() {}
                },
            );
        let mut proc = mock_proc(rx);
        let start = Instant::now();
        let error = read_response_line(&mut proc, Duration::from_millis(25))
            .expect_err("continuously ready comments must still time out");
        assert!(error.contains("timeout"));
        assert!(start.elapsed() < Duration::from_secs(1));
        drop(proc);
        producer.join().expect("comment producer exits after receiver drop");
    }

    #[test]
    fn test_model_output_size_cap() {
        assert_eq!(MAX_MODEL_OUTPUT_BYTES, 10 * 1024 * 1024);

        let mut line = std::io::Cursor::new(b"123456789\n".to_vec());
        assert!(
            read_bounded_solver_line(&mut line, 8)
                .expect_err("oversized incremental line must be rejected")
                .contains("exceeded")
        );

        let stream = std::io::Cursor::new(vec![b'x'; 9]);
        assert!(
            read_bounded_solver_stream(stream, "stdout", 8)
                .expect_err("oversized one-shot output must be rejected")
                .contains("exceeded")
        );
    }

    // -- Bounded balanced-response tests --

    /// Build a mock SolverProcess whose reader channel is `rx`, mirroring the
    /// existing read_response_line tests (Command::new("true"), mpsc mock).
    fn mock_proc(rx: mpsc::Receiver<Result<String, String>>) -> SolverProcess {
        SolverProcess {
            child: Command::new("true").spawn().expect("spawn true"),
            group_isolated: false,
            stdin: Command::new("true")
                .stdin(Stdio::piped())
                .spawn()
                .expect("spawn true for stdin")
                .stdin
                .take()
                .expect("stdin"),
            line_rx: rx,
            _reservation: crate::coordinator::Reservation::inert(),
        }
    }

    #[test]
    fn test_read_model_response_captures_multiline_balanced_expression() {
        // A representative multi-line S-expression. The reader
        // delivers it line-by-line through the mpsc mock, exactly as the real
        // reader thread would. read_model_response must reassemble the full,
        // balanced S-expression intact (no truncation, no early break).
        let proof_lines = [
            "(\n",
            "(assume a0 (not (= x y)))\n",
            "(step t1 (cl (= x y)) :rule eq_transitive)\n",
            "(step t2 (cl (and (= x y) (not (= x y)))) :rule resolution :premises (a0 t1))\n",
            "(step t3 (cl) :rule false :premises (t2))\n",
            ")\n",
        ];
        let expected: String = proof_lines.concat();

        let (tx, rx) = mpsc::channel();
        for line in proof_lines {
            tx.send(Ok(line.to_string())).unwrap();
        }

        let mut proc = mock_proc(rx);
        let result = read_model_response(&mut proc, Duration::from_secs(1));
        assert!(result.is_ok(), "should read balanced proof: {result:?}");
        let captured = result.unwrap();
        assert_eq!(captured, expected, "full proof S-expression must be intact");

        // Balanced: equal parens, and recognized as a real proof.
        let opens = captured.matches('(').count();
        let closes = captured.matches(')').count();
        assert_eq!(opens, closes, "captured proof must be balanced");
        drop(proc);
    }

    // -- Shared-prefix batch: equivalence + base-scope reset tests --
    //
    // These tests run WITHOUT a live solver: they prove that the split the
    // batch path performs is logically equivalent to the old per-VC
    // pre-conjoined path (same conjunct set ⇒ same formula ⇒ same verdict), and
    // that the per-function base scope is reset between functions.

    fn le_var(name: &str, k: i128) -> Formula {
        Formula::Le(Box::new(int_var(name)), Box::new(Formula::Int(k)))
    }

    fn vc_for(function: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: function.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// The SET of top-level conjuncts the solver effectively decides — the
    /// equivalence the batch must preserve. The trivial-true conjunct is the
    /// identity of `∧` (`A ∧ true ≡ A`), so it is normalized away.
    fn conjunct_set(f: &Formula) -> std::collections::BTreeSet<String> {
        flatten_conjuncts(f)
            .iter()
            .filter(|c| !matches!(c, Formula::Bool(true)))
            .map(|c| c.to_smtlib())
            .collect()
    }

    #[test]
    fn split_shared_prefix_extracts_common_conjuncts() {
        // Function `f` with a shared prefix [a<=10, b<=10] and two obligations:
        // one VALID under the prefix (a<=5 is NOT entailed but that is the
        // solver's job), one obviously different. We only check the SPLIT here.
        let pa = le_var("a", 10);
        let pb = le_var("b", 10);
        let o0 = le_var("a", 5);
        let o1 = Formula::Gt(Box::new(int_var("b")), Box::new(Formula::Int(100)));

        let v0 = vc_for("f", Formula::And(vec![pa.clone(), pb.clone(), o0.clone()]));
        let v1 = vc_for("f", Formula::And(vec![pa.clone(), pb.clone(), o1.clone()]));

        let (prefix, bare) = split_shared_prefix(&[v0, v1]);

        let prefix_set: std::collections::BTreeSet<String> =
            prefix.iter().map(|c| c.to_smtlib()).collect();
        assert_eq!(prefix.len(), 2, "exactly the two shared facts are hoisted");
        assert!(prefix_set.contains(&pa.to_smtlib()));
        assert!(prefix_set.contains(&pb.to_smtlib()));

        // The bare obligations carry ONLY their delta (prefix dropped).
        assert_eq!(conjunct_set(&bare[0].formula), conjunct_set(&o0));
        assert_eq!(conjunct_set(&bare[1].formula), conjunct_set(&o1));
    }

    #[test]
    fn split_is_logically_equivalent_to_preconjoined_for_valid_and_invalid() {
        // A VALID obligation (prefix entails it) and an INVALID one (prefix
        // refutes it) must BOTH reconstruct, byte-for-byte at the conjunct-set
        // level, to the original pre-conjoined formula the per-VC path solves.
        let prefix_fact = le_var("x", 7); // x <= 7
        let valid_obl = le_var("x", 10); // x <= 10 (entailed: PROVED both ways)
        let invalid_obl = le_var("x", 3); // x <= 3 (NOT entailed: FAILED both ways)

        let valid_full = Formula::And(vec![prefix_fact.clone(), valid_obl.clone()]);
        let invalid_full = Formula::And(vec![prefix_fact.clone(), invalid_obl.clone()]);

        let v_valid = vc_for("g", valid_full.clone());
        let v_invalid = vc_for("g", invalid_full.clone());

        let (prefix, bare) = split_shared_prefix(&[v_valid, v_invalid]);

        for (orig_full, bare_vc) in [&valid_full, &invalid_full].into_iter().zip(bare.iter()) {
            // Reassemble exactly what the solver decides on the batch path:
            // base-scope prefix conjoined with the bare obligation.
            let mut reassembled = prefix.clone();
            reassembled.extend(flatten_conjuncts(&bare_vc.formula));
            let reassembled = conjoin_formulas(reassembled);

            assert_eq!(
                conjunct_set(orig_full),
                conjunct_set(&reassembled),
                "batch path must decide the SAME conjunct set as the per-VC path"
            );
        }
    }

    #[test]
    fn split_yields_distinct_prefixes_per_function_group() {
        // Two different functions get DIFFERENT shared prefixes; one function's
        // prefix must never appear in the other's split.
        let f_a = vc_for("fa", Formula::And(vec![le_var("a", 1), le_var("a", 2)]));
        let f_b = vc_for("fb", Formula::And(vec![le_var("b", 9), le_var("b", 8)]));

        let (prefix_a, _) = split_shared_prefix(&[f_a.clone()]);
        let (prefix_b, _) = split_shared_prefix(&[f_b.clone()]);

        let set_a: std::collections::BTreeSet<String> =
            prefix_a.iter().map(|c| c.to_smtlib()).collect();
        let set_b: std::collections::BTreeSet<String> =
            prefix_b.iter().map(|c| c.to_smtlib()).collect();
        assert!(set_a.is_disjoint(&set_b), "distinct functions ⇒ disjoint prefixes");
    }

    #[test]
    fn set_prefix_replaces_and_forces_reinitialization() {
        let session = IncrementalAYSession::new();

        let prefix_a = vec![CommonAssertion::from_formula("pa", &le_var("a", 10))];
        let prefix_b = vec![CommonAssertion::from_formula("pb", &le_var("b", 20))];

        {
            let mut st = session.state.lock().unwrap();
            // Pretend the base was already sent.
            st.base_initialized = true;
            st.set_prefix(prefix_a, Some("QF_LIA".to_string()));
            assert_eq!(st.current_prefix.len(), 1);
            assert!(st.prefix_declared_vars.contains("a"));
            assert!(!st.prefix_declared_vars.contains("b"));
            assert!(!st.base_initialized, "new prefix forces base re-init");

            // Installing function B's prefix REPLACES A's (no leak across funcs).
            st.base_initialized = true;
            st.set_prefix(prefix_b, Some("QF_LIA".to_string()));
            assert_eq!(st.current_prefix.len(), 1);
            assert!(st.prefix_declared_vars.contains("b"));
            assert!(
                !st.prefix_declared_vars.contains("a"),
                "function A's declared vars must not survive into function B"
            );
            assert!(!st.base_initialized);

            // Clearing the prefix (empty) resets the base scope entirely.
            st.base_initialized = true;
            st.set_prefix(Vec::new(), None);
            assert!(st.current_prefix.is_empty());
            assert!(st.prefix_declared_vars.is_empty());
            assert!(!st.base_initialized);
        }
    }

    #[test]
    fn verify_batch_resets_prefix_after_completion() {
        let _memory_authority = unconfigured_memory_authority();
        // No solver on PATH ⇒ every query falls back, but the batch must STILL
        // leave the session's base scope EMPTY when it finishes, so a later
        // plain `verify` is never decided against a stale prefix.
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_xyz");
        let vcs = vec![
            vc_for("h", Formula::And(vec![le_var("a", 10), le_var("a", 5)])),
            vc_for("h", Formula::And(vec![le_var("a", 10), le_var("a", 3)])),
        ];

        let results = session.verify_batch(&vcs);
        assert_eq!(results.len(), 2);

        let st = session.state.lock().unwrap();
        assert!(st.current_prefix.is_empty(), "prefix must be cleared after the batch");
        assert!(st.prefix_declared_vars.is_empty());
    }

    #[test]
    fn verify_batch_returns_original_full_vcs_in_input_order() {
        let _memory_authority = unconfigured_memory_authority();
        // The returned VCs must carry the ORIGINAL pre-conjoined formula (so a
        // downstream cache keying on `vc.formula` is unaffected by the split),
        // in input order, across multiple function groups.
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_xyz");
        let full0 = Formula::And(vec![le_var("a", 10), le_var("a", 5)]);
        let full1 = Formula::And(vec![le_var("b", 9), le_var("b", 1)]);
        let full2 = Formula::And(vec![le_var("a", 10), le_var("a", 4)]);
        let vcs = vec![
            vc_for("f1", full0.clone()),
            vc_for("f2", full1.clone()),
            vc_for("f1", full2.clone()),
        ];

        let results = session.verify_batch(&vcs);
        assert_eq!(results.len(), 3);
        // Returned formulas are the FULL originals (prefix NOT stripped), in order.
        assert_eq!(conjunct_set(&results[0].0.formula), conjunct_set(&full0));
        assert_eq!(conjunct_set(&results[1].0.formula), conjunct_set(&full1));
        assert_eq!(conjunct_set(&results[2].0.formula), conjunct_set(&full2));
        assert_eq!(results[0].0.function, "f1");
        assert_eq!(results[1].0.function, "f2");
        assert_eq!(results[2].0.function, "f1");
    }

    #[test]
    fn set_prefix_change_kills_live_process_and_same_prefix_is_noop() {
        let _memory_authority = unconfigured_memory_authority();
        // Trust: S2 stage (C) hardening regression. Base-scope commands are
        // top-level (never popped), so a prefix CHANGE on a live process must
        // KILL it — re-sending a new base to the same process would append onto
        // the old one (stale cross-function facts = false-proof channel,
        // duplicate declarations, a second `set-logic`). An IDENTICAL prefix is
        // a no-op: the live process's base already matches.
        let session = IncrementalAYSession::with_solver_path("/bin/cat");
        let prefix_a = vec![CommonAssertion::from_formula("pa", &le_var("a", 10))];
        let prefix_b = vec![CommonAssertion::from_formula("pb", &le_var("b", 20))];

        let mut st = session.state.lock().unwrap();

        // Live process + installed prefix A.
        st.process = Some(session.spawn_solver().expect("spawn /bin/cat as a fake solver"));
        st.base_initialized = true;
        st.set_prefix(prefix_a.clone(), Some("QF_LIA".to_string()));
        assert!(st.process.is_none(), "prefix change (empty -> A) must kill the live process");
        assert!(!st.base_initialized);

        // Re-installing the SAME prefix + logic is a no-op: process retained,
        // no forced re-init (the base scope already holds exactly this prefix).
        st.process = Some(session.spawn_solver().expect("spawn /bin/cat as a fake solver"));
        st.base_initialized = true;
        st.set_prefix(prefix_a.clone(), Some("QF_LIA".to_string()));
        assert!(st.process.is_some(), "identical prefix+logic is a no-op: process kept");
        assert!(st.base_initialized, "no re-init when the base content is unchanged");

        // Changing to prefix B kills; so does clearing (B -> empty).
        st.set_prefix(prefix_b, Some("QF_LIA".to_string()));
        assert!(st.process.is_none(), "prefix change (A -> B) must kill the live process");
        st.process = Some(session.spawn_solver().expect("spawn /bin/cat as a fake solver"));
        st.base_initialized = true;
        st.set_prefix(Vec::new(), None);
        assert!(st.process.is_none(), "prefix clear (B -> empty) must kill the live process");
        st.kill_process();
    }

    #[test]
    fn verify_batch_pins_session_logic_once_from_first_full_formula() {
        let _memory_authority = unconfigured_memory_authority();
        // Trust: batch mode must pin ONE session logic (from the first batched
        // VC's FULL formula — what the per-VC path's single base init would
        // auto-detect) and keep it across later batch calls, so base re-inits
        // at group boundaries cannot flap the logic and flip verdicts.
        let session = IncrementalAYSession::with_solver_path("nonexistent_solver_xyz");
        let first = vc_for("f1", Formula::And(vec![le_var("a", 10), le_var("a", 5)]));
        let expected = smt2_export::detect_logic(&first.formula).to_string();

        let _ = session.verify_batch(std::slice::from_ref(&first));
        {
            let st = session.state.lock().unwrap();
            assert_eq!(st.batch_pinned_logic.as_deref(), Some(expected.as_str()));
        }

        // A later batch with a different-theory formula must NOT re-pin.
        let bv = vc_for(
            "f2",
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::BitVec(64))),
                Box::new(Formula::BitVec { value: 3, width: 64 }),
            ))),
        );
        let _ = session.verify_batch(std::slice::from_ref(&bv));
        let st = session.state.lock().unwrap();
        assert_eq!(
            st.batch_pinned_logic.as_deref(),
            Some(expected.as_str()),
            "the session logic is pinned once, like the per-VC path's"
        );
    }

    /// Trust: S2 stage (C) end-to-end engagement + isolation regression against
    /// the REAL `ay` solver (skips when `ay` is not spawnable).
    ///
    /// - Group `fa` (M=2, shared conjunct `x <= 2`) exercises the HOIST path:
    ///   `fa1`'s bare obligation (`x > 9`) is SAT on its own, so its `Proved`
    ///   verdict proves the hoisted prefix genuinely reached the solver's base
    ///   scope (a dropped prefix would yield `Failed`).
    /// - Group `fb` runs AFTER `fa` on the same session; its obligations are
    ///   SAT with fb's own prefix (`x > 49`) but would be UNSAT — falsely
    ///   `Proved` — if fa's stale `x <= 2` leaked into the base scope (the
    ///   colliding-name bleed the `set_prefix` kill fix closes; on the pre-fix
    ///   code this test fails).
    /// - Every verdict must match a fresh session's per-VC dispatch.
    #[test]
    fn batch_hoist_verdicts_match_per_vc_and_never_leak_prefix_with_real_ay() {
        let _memory_authority = unconfigured_memory_authority();
        if std::process::Command::new("ay")
            .arg("--version")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_err()
        {
            eprintln!("skipping: `ay` not spawnable on PATH");
            return;
        }

        let gt_var =
            |name: &str, k: i128| Formula::Gt(Box::new(int_var(name)), Box::new(Formula::Int(k)));
        let fa1 = vc_for("fa", Formula::And(vec![le_var("x", 2), gt_var("x", 9)]));
        let fa2 = vc_for("fa", Formula::And(vec![le_var("x", 2), gt_var("x", -5)]));
        let fb1 = vc_for("fb", Formula::And(vec![gt_var("x", 49), le_var("x", 60)]));
        let fb2 = vc_for("fb", Formula::And(vec![gt_var("x", 49), le_var("x", 55)]));
        let vcs = vec![fa1, fa2, fb1, fb2];

        let batch_session = IncrementalAYSession::new();
        let batched = batch_session.verify_batch(&vcs);
        assert_eq!(batched.len(), 4);

        let pervc_session = IncrementalAYSession::new();
        let per_vc: Vec<VerificationResult> =
            vcs.iter().map(|vc| pervc_session.verify_vc(vc)).collect();

        let kind = |r: &VerificationResult| match r {
            VerificationResult::Proved { .. } => "proved",
            VerificationResult::Failed { .. } => "failed",
            VerificationResult::Unknown { .. } => "unknown",
            VerificationResult::Timeout { .. } => "timeout",
            _ => "other",
        };

        // Expected ground truth (violation semantics: unsat => Proved).
        let expected = ["proved", "failed", "failed", "failed"];
        for (i, want) in expected.iter().enumerate() {
            assert_eq!(
                kind(&batched[i].1),
                *want,
                "batch verdict for vc[{i}] (fa1 Proved proves the hoisted prefix \
                 was asserted; fb Failed proves fa's prefix did not leak): {:#?}",
                batched[i].1,
            );
            assert_eq!(
                kind(&per_vc[i]),
                *want,
                "per-VC verdict for vc[{i}] must match the same ground truth"
            );
        }
    }

    #[test]
    fn flatten_and_conjoin_round_trip_preserves_conjunct_set() {
        let f =
            Formula::And(vec![le_var("a", 1), Formula::And(vec![le_var("b", 2), le_var("c", 3)])]);
        let flat = flatten_conjuncts(&f);
        assert_eq!(flat.len(), 3, "nested And flattens to 3 conjuncts");
        assert_eq!(conjunct_set(&conjoin_formulas(flat)), conjunct_set(&f));
        // Empty conjunction is trivial-true; singleton is bare.
        assert_eq!(conjoin_formulas(Vec::new()), Formula::Bool(true));
        assert_eq!(conjoin_formulas(vec![le_var("a", 1)]), le_var("a", 1));
    }

    // -- Lever A: datatype/sort declarations on the incremental lane --
    //
    // `emit_declarations` now also returns `(declare-sort …)` and
    // `(declare-datatype …)`. Those bind a name in the same solver namespace a
    // variable does, so the incremental lane's base-scope/push-scope
    // de-duplication must see them: the shared prefix and every bare obligation
    // that mentions an `Expr`-sorted variable BOTH emit the identical
    // `(declare-datatype Expr …)`, and sending it twice is a redeclaration
    // error that kills the session (verdicts stay sound — the fallback solves
    // the FULL formula per-process — but the session churns restarts and can end
    // up `permanently_fallen_back`).

    /// A recursive `Expr` datatype: a `Leaf(i)` base case and a binary
    /// `Node(l, r)` whose children are BY-NAME references back to `Expr` (the
    /// natively-recursive SMT-LIB datatype encoding Lever A emits).
    fn expr_sort() -> Sort {
        let expr_ref = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Leaf".into(), vec![("i".into(), Sort::Int)]),
                ("Node".into(), vec![("l".into(), expr_ref.clone()), ("r".into(), expr_ref)]),
            ],
        }
    }

    /// `a = b` over two `Expr`-sorted variables — a formula whose SMT preamble
    /// carries a datatype declaration.
    fn expr_eq(a: &str, b: &str) -> Formula {
        Formula::Eq(
            Box::new(Formula::Var(a.into(), expr_sort())),
            Box::new(Formula::Var(b.into(), expr_sort())),
        )
    }

    /// REGRESSION (no test covered this path): the per-VC push scope must NOT
    /// re-declare a datatype the base-scope prefix already declared.
    #[test]
    fn push_scope_skips_a_datatype_the_base_prefix_declared() {
        let session = IncrementalAYSession::new();
        // Two obligations of one function sharing the datatype-bearing conjunct.
        let shared = expr_eq("e", "f");
        let vcs = vec![
            vc_for("g", Formula::And(vec![shared.clone(), expr_eq("e", "g1")])),
            vc_for("g", Formula::And(vec![shared, expr_eq("e", "g2")])),
        ];
        let (prefix_formulas, bare_vcs) = split_shared_prefix(&vcs);
        assert_eq!(prefix_formulas.len(), 1, "the datatype-bearing conjunct is shared");

        let prefix: Vec<CommonAssertion> = prefix_formulas
            .iter()
            .enumerate()
            .map(|(i, f)| CommonAssertion::from_formula(format!("shared-prefix-{i}"), f))
            .collect();
        let base_commands: Vec<String> =
            prefix.iter().flat_map(|a| a.commands.iter().cloned()).collect();
        assert!(
            base_commands.iter().any(|c| c.starts_with("(declare-datatype Expr ")),
            "the base scope declares the datatype: {base_commands:?}"
        );

        let base_declared = {
            let mut st = session.state.lock().unwrap();
            st.set_prefix(prefix, Some("ALL".to_string()));
            assert!(
                st.prefix_declared_vars.contains("Expr"),
                "a datatype name is a base-scope declaration identity, like a variable"
            );
            st.prefix_declared_vars.clone()
        };

        // Exactly what `verify_incremental` sends inside `(push 1)`.
        let scoped = scope_declarations(&bare_vcs[0].formula, &base_declared);
        assert!(
            !scoped.iter().any(|c| c.starts_with("(declare-datatype Expr ")),
            "redeclaring the base-scope datatype inside push/pop errors the session: {scoped:?}"
        );
        assert!(
            !scoped.iter().any(|c| c.starts_with("(declare-fun e ")),
            "the base-scope VARIABLE stays skipped (unchanged behavior): {scoped:?}"
        );
        assert!(
            scoped.iter().any(|c| c.starts_with("(declare-fun g1 ")),
            "the obligation's own variable is still declared in its scope: {scoped:?}"
        );

        // Whole-session view: the datatype is declared exactly ONCE.
        let all: Vec<String> = base_commands.into_iter().chain(scoped).collect();
        assert_eq!(
            all.iter().filter(|c| c.starts_with("(declare-datatype Expr ")).count(),
            1,
            "one declaration of `Expr` across base scope + push scope: {all:?}"
        );
    }

    /// A stand-in solver that RECORDS every command it is sent and answers
    /// `(check-sat)` with `unknown` (the branch that pops and returns without a
    /// model or a proof), so a test can assert on the exact command stream the
    /// incremental session emits.
    #[cfg(unix)]
    struct RecordingSolver {
        directory: std::path::PathBuf,
        script: std::path::PathBuf,
        log: std::path::PathBuf,
    }

    #[cfg(unix)]
    impl RecordingSolver {
        fn new(label: &str) -> Self {
            use std::os::unix::fs::PermissionsExt as _;

            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos();
            let directory = std::env::temp_dir()
                .join(format!("trust-recording-solver-{label}-{}-{nonce:x}", std::process::id()));
            std::fs::create_dir_all(&directory).expect("create recording solver fixture");
            std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))
                .expect("make recording solver fixture private");
            let log = directory.join("commands.log");
            let script = directory.join("solver.sh");
            std::fs::write(
                &script,
                format!(
                    "#!/bin/sh\n\
                     while IFS= read -r line; do\n\
                     \x20 printf '%s\\n' \"$line\" >> '{}'\n\
                     \x20 if [ \"$line\" = '(check-sat)' ]; then printf 'unknown\\n'; fi\n\
                     done\n",
                    log.display()
                ),
            )
            .expect("write recording solver");
            std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o700))
                .expect("make recording solver executable");
            Self { directory, script, log }
        }

        /// Every command the session sent, in order.
        fn commands(&self) -> Vec<String> {
            std::fs::read_to_string(&self.log)
                .unwrap_or_default()
                .lines()
                .map(str::to_string)
                .collect()
        }
    }

    #[cfg(unix)]
    impl Drop for RecordingSolver {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.log);
            let _ = std::fs::remove_file(&self.script);
            let _ = std::fs::remove_dir(&self.directory);
        }
    }

    /// REGRESSION, end to end: drive two datatype-bearing obligations of one
    /// function through `verify_batch` against a recording solver and assert the
    /// datatype reaches the solver exactly ONCE — at the base scope, before the
    /// first `(push 1)` — with no session fault or fallback.
    #[cfg(unix)]
    #[test]
    fn batch_lane_sends_a_datatype_declaration_exactly_once() {
        let _memory_authority = unconfigured_memory_authority();
        let fixture = RecordingSolver::new("datatype-once");
        let session = IncrementalAYSession::with_solver_path(
            fixture.script.to_str().expect("utf-8 fixture path"),
        );
        let shared = expr_eq("e", "f");
        let vcs = vec![
            vc_for("g", Formula::And(vec![shared.clone(), expr_eq("e", "g1")])),
            vc_for("g", Formula::And(vec![shared, expr_eq("e", "g2")])),
        ];

        let results = session.verify_batch(&vcs);
        assert_eq!(results.len(), 2);

        let commands = fixture.commands();
        let pushes = commands.iter().filter(|c| c.trim() == "(push 1)").count();
        assert_eq!(pushes, 2, "both obligations ran as push/pop scopes: {commands:?}");
        assert_eq!(
            commands.iter().filter(|c| c.starts_with("(declare-datatype Expr ")).count(),
            1,
            "the datatype must be declared ONCE; a redeclaration inside push/pop \
             errors the session: {commands:?}"
        );
        let declared_at = commands
            .iter()
            .position(|c| c.starts_with("(declare-datatype Expr "))
            .expect("the datatype must reach the solver at all");
        let first_push =
            commands.iter().position(|c| c.trim() == "(push 1)").expect("a push scope ran");
        assert!(
            declared_at < first_push,
            "the datatype belongs to the BASE scope, ahead of every push: {commands:?}"
        );

        let stats = session.stats();
        assert_eq!(stats.restarts, 0, "no session fault: {commands:?}");
        assert_eq!(stats.incremental_queries, 2, "both queries stayed incremental: {commands:?}");
        assert_eq!(stats.fallback_queries, 0, "no per-process fallback: {commands:?}");
    }

    /// A promoted `(declare-fun e () Expr)` is malformed unless `Expr` is
    /// promoted with it, and ahead of it.
    #[test]
    fn extract_common_declarations_promotes_datatypes_before_their_users() {
        let mut session = IncrementalAYSession::new();
        let vcs = vec![make_vc(expr_eq("e", "a")), make_vc(expr_eq("e", "b"))];

        session.extract_common_declarations(&vcs);

        assert_eq!(session.stats().common_assertions, 1);
        let commands = &session.common_assertions[0].commands;
        // `Expr` and `e` both appear in 2 VCs, so both are promoted — and the
        // sort must land ahead of the `declare-fun` that uses it.
        let datatype = commands.iter().position(|c| c.starts_with("(declare-datatype Expr "));
        let variable = commands.iter().position(|c| c.starts_with("(declare-fun e "));
        assert!(
            matches!((datatype, variable), (Some(sort), Some(var)) if sort < var),
            "the promoted variable's datatype must be promoted with it, and declared \
             before it: {commands:?}"
        );
        assert!(
            !commands.iter().any(|c| c.starts_with("(declare-fun a ")),
            "a variable in only ONE VC is not promoted: {commands:?}"
        );
    }
}
