// trust-types/concurrency.rs: Concurrency model types for temporal verification
//
// Represents concurrency primitives (Mutex, RwLock, Channel, async) extracted
// from MIR. Used by trust-mir-extract to build process algebra models and by
// downstream TLA+ generation for deadlock/liveness checking.
//
// Part of #48: Concurrency model extraction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::{FxHashMap, FxHashSet};
use std::fmt::Write;

use serde::{Deserialize, Serialize};

use crate::{BlockId, SourceSpan};

/// A concurrency primitive detected in MIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConcurrencyPrimitive {
    /// std::sync::Mutex
    Mutex,
    /// std::sync::RwLock
    RwLock,
    /// std::sync::mpsc channel (or crossbeam)
    Channel,
    /// std::sync::Condvar
    Condvar,
    /// std::sync::atomic::*
    Atomic,
    /// tokio::sync::Semaphore
    Semaphore,
    /// tokio::sync::Notify
    Notify,
    /// tokio::spawn / async task spawn
    AsyncSpawn,
}

/// An operation on a concurrency primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConcurrencyOperation {
    /// Acquire a lock (Mutex::lock, RwLock::write)
    Lock,
    /// Acquire a read lock (RwLock::read)
    ReadLock,
    /// Attempt to acquire (try_lock, try_read, try_write)
    TryLock,
    /// Release (implicit via Drop, or explicit unlock)
    Unlock,
    /// Send a message on a channel
    Send,
    /// Receive a message from a channel
    Recv,
    /// Create a new channel
    ChannelCreate,
    /// Wait on a condvar
    CondvarWait,
    /// Notify a condvar
    CondvarNotify,
    /// Atomic load
    AtomicLoad,
    /// Atomic store
    AtomicStore,
    /// Atomic compare-and-swap / compare_exchange
    AtomicCas,
    /// Atomic fence
    AtomicFence,
    /// Spawn an async task / thread
    Spawn,
    /// Semaphore acquire
    SemaphoreAcquire,
    /// Semaphore release
    SemaphoreRelease,
    /// Notify::notify_one / notify_waiters
    NotifySignal,
    /// Notify::notified (wait)
    NotifyWait,
}

/// Identifier for a shared resource in the concurrency model.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ResourceId(pub String);

/// A shared resource participating in concurrency.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SharedResource {
    /// Unique identifier derived from the MIR local or def path.
    pub id: ResourceId,
    /// What kind of concurrency primitive this resource is.
    pub primitive: ConcurrencyPrimitive,
    /// Human-readable name (variable name if available).
    pub name: Option<String>,
    /// Type of the protected data (e.g., `Mutex<Vec<i32>>`).
    pub guarded_type: Option<String>,
}

/// A concurrency event: an operation on a shared resource at a specific MIR location.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcurrencyEvent {
    /// The operation performed.
    pub operation: ConcurrencyOperation,
    /// The resource involved.
    pub resource_id: ResourceId,
    /// MIR block where this event occurs.
    pub block: BlockId,
    /// Source location.
    pub span: SourceSpan,
    /// The full function call path that was matched (for diagnostics).
    pub call_path: String,
}

/// A complete concurrency model for one function.
///
/// Lists shared resources and the sequence of concurrency events found in MIR.
/// This is the input for TLA+ model generation and deadlock analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConcurrencyModel {
    /// Shared resources referenced by this function.
    pub resources: Vec<SharedResource>,
    /// Ordered sequence of concurrency events (in MIR block order).
    pub events: Vec<ConcurrencyEvent>,
    /// Function this model was extracted from.
    pub function: String,
}

impl ConcurrencyModel {
    /// Create an empty concurrency model for a function.
    pub fn new(function: impl Into<String>) -> Self {
        Self { resources: Vec::new(), events: Vec::new(), function: function.into() }
    }

    /// Returns true if no concurrency operations were detected.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Add a shared resource to the model. Returns the resource ID.
    pub fn add_resource(&mut self, resource: SharedResource) -> ResourceId {
        let id = resource.id.clone();
        if !self.resources.iter().any(|r| r.id == id) {
            self.resources.push(resource);
        }
        id
    }

    /// Add a concurrency event.
    pub fn add_event(&mut self, event: ConcurrencyEvent) {
        self.events.push(event);
    }

    /// Detect potential deadlocks from lock ordering violations.
    ///
    /// Returns pairs of resources that are acquired in inconsistent order,
    /// which could lead to circular wait (a necessary condition for deadlock).
    ///
    /// This is a conservative analysis: it reports any pair of locks where
    /// lock A is acquired before lock B in one path AND lock B before lock A
    /// in another path within the same function (or across functions if
    /// multiple models are combined).
    pub fn detect_lock_order_violations(&self) -> Vec<LockOrderViolation> {
        // Build lock acquisition sequences per resource
        let lock_ops: Vec<&ConcurrencyEvent> = self
            .events
            .iter()
            .filter(|e| {
                matches!(
                    e.operation,
                    ConcurrencyOperation::Lock
                        | ConcurrencyOperation::ReadLock
                        | ConcurrencyOperation::TryLock
                )
            })
            .collect();

        if lock_ops.len() < 2 {
            return Vec::new();
        }

        // Check for inconsistent ordering: for every pair (A, B), check if
        // A appears before B in one sequence and B before A in another.
        // Within a single function this means: if we see lock(A) then lock(B)
        // at blocks i < j, that establishes order A->B.
        let mut order_pairs: FxHashSet<(ResourceId, ResourceId)> = FxHashSet::default();
        let mut violations = Vec::new();

        for (i, first) in lock_ops.iter().enumerate() {
            for second in lock_ops.iter().skip(i + 1) {
                if first.resource_id == second.resource_id {
                    continue;
                }
                let pair = (first.resource_id.clone(), second.resource_id.clone());
                let reverse = (second.resource_id.clone(), first.resource_id.clone());

                if order_pairs.contains(&reverse) {
                    violations.push(LockOrderViolation {
                        resource_a: first.resource_id.clone(),
                        resource_b: second.resource_id.clone(),
                        first_acquisition: first.span.clone(),
                        second_acquisition: second.span.clone(),
                    });
                }
                order_pairs.insert(pair);
            }
        }

        violations
    }

    /// Get all resources of a specific primitive type.
    pub fn resources_of_type(&self, primitive: ConcurrencyPrimitive) -> Vec<&SharedResource> {
        self.resources.iter().filter(|r| r.primitive == primitive).collect()
    }

    /// Get all events for a specific resource.
    pub fn events_for_resource(&self, resource_id: &ResourceId) -> Vec<&ConcurrencyEvent> {
        self.events.iter().filter(|e| &e.resource_id == resource_id).collect()
    }

    /// Generate a TLA+ process algebra model from the concurrency events.
    ///
    /// Produces a TLA+ module with:
    /// - Variables for lock state, channel buffers, program counters
    /// - Init predicate
    /// - Next-state relation from concurrency operations
    /// - Deadlock freedom property
    /// - Channel liveness property
    pub fn to_tla_plus(&self) -> String {
        let mut tla = String::new();
        let module_name = sanitize_tla_name(&self.function);

        // Module header
        let _ = writeln!(tla, "---- MODULE {module_name} ----");
        tla.push_str("EXTENDS Integers, Sequences, FiniteSets\n\n");

        // Constants
        tla.push_str("CONSTANTS Threads\n\n");

        // Variables
        let mut vars = Vec::new();

        // Lock state variables
        let mutexes = self.resources_of_type(ConcurrencyPrimitive::Mutex);
        let rwlocks = self.resources_of_type(ConcurrencyPrimitive::RwLock);
        let channels = self.resources_of_type(ConcurrencyPrimitive::Channel);

        for m in &mutexes {
            let var = sanitize_tla_name(&m.id.0);
            vars.push(format!("held_{var}"));
        }
        for rw in &rwlocks {
            let var = sanitize_tla_name(&rw.id.0);
            vars.push(format!("readers_{var}"));
            vars.push(format!("writer_{var}"));
        }
        for ch in &channels {
            let var = sanitize_tla_name(&ch.id.0);
            vars.push(format!("buffer_{var}"));
        }
        vars.push("pc".to_string());

        if vars.is_empty() {
            tla.push_str("VARIABLES pc\n\n");
        } else {
            tla.push_str("VARIABLES ");
            tla.push_str(&vars.join(", "));
            tla.push_str("\n\n");
        }

        let _ = write!(tla, "vars == << {} >>\n\n", vars.join(", "));

        // Init predicate
        tla.push_str("Init ==\n");
        for m in &mutexes {
            let var = sanitize_tla_name(&m.id.0);
            let _ = writeln!(tla, "    /\\ held_{var} = \"none\"");
        }
        for rw in &rwlocks {
            let var = sanitize_tla_name(&rw.id.0);
            let _ = writeln!(tla, "    /\\ readers_{var} = {{}}");
            let _ = writeln!(tla, "    /\\ writer_{var} = \"none\"");
        }
        for ch in &channels {
            let var = sanitize_tla_name(&ch.id.0);
            let _ = writeln!(tla, "    /\\ buffer_{var} = << >>");
        }
        tla.push_str("    /\\ pc = [t \\in Threads |-> \"start\"]\n\n");

        // Actions for each operation type
        let mut actions = Vec::new();

        for m in &mutexes {
            let var = sanitize_tla_name(&m.id.0);
            let action_name = format!("Lock_{var}");
            let _ = write!(
                tla,
                "{action_name}(t) ==\n    /\\ held_{var} = \"none\"\n    /\\ held_{var}' = t\n    /\\ UNCHANGED << {} >>\n\n",
                unchanged_except(&vars, &[&format!("held_{var}")])
            );

            let unlock_name = format!("Unlock_{var}");
            let _ = write!(
                tla,
                "{unlock_name}(t) ==\n    /\\ held_{var} = t\n    /\\ held_{var}' = \"none\"\n    /\\ UNCHANGED << {} >>\n\n",
                unchanged_except(&vars, &[&format!("held_{var}")])
            );

            actions.push(format!("\\E t \\in Threads: {action_name}(t)"));
            actions.push(format!("\\E t \\in Threads: {unlock_name}(t)"));
        }

        for rw in &rwlocks {
            let var = sanitize_tla_name(&rw.id.0);
            let read_name = format!("ReadLock_{var}");
            let _ = write!(
                tla,
                "{read_name}(t) ==\n    /\\ writer_{var} = \"none\"\n    /\\ readers_{var}' = readers_{var} \\union {{t}}\n    /\\ UNCHANGED << {} >>\n\n",
                unchanged_except(&vars, &[&format!("readers_{var}")])
            );

            let write_name = format!("WriteLock_{var}");
            let _ = write!(
                tla,
                "{write_name}(t) ==\n    /\\ writer_{var} = \"none\"\n    /\\ readers_{var} = {{}}\n    /\\ writer_{var}' = t\n    /\\ UNCHANGED << {} >>\n\n",
                unchanged_except(&vars, &[&format!("writer_{var}")])
            );

            actions.push(format!("\\E t \\in Threads: {read_name}(t)"));
            actions.push(format!("\\E t \\in Threads: {write_name}(t)"));
        }

        for ch in &channels {
            let var = sanitize_tla_name(&ch.id.0);
            let send_name = format!("Send_{var}");
            let _ = write!(
                tla,
                "{send_name}(t, msg) ==\n    /\\ buffer_{var}' = Append(buffer_{var}, msg)\n    /\\ UNCHANGED << {} >>\n\n",
                unchanged_except(&vars, &[&format!("buffer_{var}")])
            );

            let recv_name = format!("Recv_{var}");
            let _ = write!(
                tla,
                "{recv_name}(t) ==\n    /\\ Len(buffer_{var}) > 0\n    /\\ buffer_{var}' = Tail(buffer_{var})\n    /\\ UNCHANGED << {} >>\n\n",
                unchanged_except(&vars, &[&format!("buffer_{var}")])
            );

            actions.push(format!("\\E t \\in Threads, msg \\in {{\"msg\"}}: {send_name}(t, msg)"));
            actions.push(format!("\\E t \\in Threads: {recv_name}(t)"));
        }

        // Next-state relation
        tla.push_str("Next ==\n");
        if actions.is_empty() {
            tla.push_str("    UNCHANGED vars\n\n");
        } else {
            for action in &actions {
                let _ = writeln!(tla, "    \\/ {action}");
            }
            tla.push('\n');
        }

        // Spec
        tla.push_str("Spec == Init /\\ [][Next]_vars\n\n");

        // Properties
        tla.push_str("\\* Deadlock freedom: some action is always enabled\n");
        tla.push_str("DeadlockFreedom == []<><<Next>>_vars\n\n");

        // Mutual exclusion for mutexes
        for m in &mutexes {
            let var = sanitize_tla_name(&m.id.0);
            let _ = write!(
                tla,
                "\\* Mutual exclusion for {var}\nMutualExclusion_{var} == \\A t1, t2 \\in Threads: (held_{var} = t1 /\\ held_{var} = t2) => t1 = t2\n\n"
            );
        }

        // Channel liveness
        for ch in &channels {
            let var = sanitize_tla_name(&ch.id.0);
            let _ = write!(
                tla,
                "\\* Channel liveness: messages eventually consumed\nChannelLiveness_{var} == [](Len(buffer_{var}) > 0 => <>(Len(buffer_{var}) = 0))\n\n"
            );
        }

        tla.push_str("====\n");
        tla
    }
}

/// A detected lock ordering violation (potential deadlock).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LockOrderViolation {
    /// First resource in the inconsistent pair.
    pub resource_a: ResourceId,
    /// Second resource in the inconsistent pair.
    pub resource_b: ResourceId,
    /// Where the first acquisition was detected.
    pub first_acquisition: SourceSpan,
    /// Where the reversed acquisition was detected.
    pub second_acquisition: SourceSpan,
}

/// Sanitize a Rust path into a valid TLA+ identifier.
fn sanitize_tla_name(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect::<String>()
        .trim_matches('_')
        .to_string()
}

/// Build an UNCHANGED clause excluding the specified variables.
fn unchanged_except(all_vars: &[String], changed: &[&str]) -> String {
    let unchanged: Vec<&String> =
        all_vars.iter().filter(|v| !changed.contains(&v.as_str())).collect();
    if unchanged.is_empty() {
        return String::new();
    }
    unchanged.iter().map(|v| v.as_str()).collect::<Vec<_>>().join(", ")
}

/// Known concurrency API patterns for matching against MIR Call func names.
///
/// Each entry maps a substring of the def_path to a (primitive, operation) pair.
/// The matching is done by checking if the Call terminator's func string contains
/// the pattern. Longest match wins when multiple patterns match.
pub const CONCURRENCY_PATTERNS: &[(&str, ConcurrencyPrimitive, ConcurrencyOperation)] = &[
    // std::sync::Mutex
    ("std::sync::Mutex::lock", ConcurrencyPrimitive::Mutex, ConcurrencyOperation::Lock),
    ("std::sync::Mutex::try_lock", ConcurrencyPrimitive::Mutex, ConcurrencyOperation::TryLock),
    // std::sync::RwLock
    ("std::sync::RwLock::read", ConcurrencyPrimitive::RwLock, ConcurrencyOperation::ReadLock),
    ("std::sync::RwLock::write", ConcurrencyPrimitive::RwLock, ConcurrencyOperation::Lock),
    ("std::sync::RwLock::try_read", ConcurrencyPrimitive::RwLock, ConcurrencyOperation::TryLock),
    ("std::sync::RwLock::try_write", ConcurrencyPrimitive::RwLock, ConcurrencyOperation::TryLock),
    // std::sync::mpsc
    ("std::sync::mpsc::Sender::send", ConcurrencyPrimitive::Channel, ConcurrencyOperation::Send),
    (
        "std::sync::mpsc::SyncSender::send",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::Send,
    ),
    ("std::sync::mpsc::Receiver::recv", ConcurrencyPrimitive::Channel, ConcurrencyOperation::Recv),
    (
        "std::sync::mpsc::Receiver::try_recv",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::Recv,
    ),
    (
        "std::sync::mpsc::channel",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::ChannelCreate,
    ),
    (
        "std::sync::mpsc::sync_channel",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::ChannelCreate,
    ),
    // std::sync::Condvar
    ("std::sync::Condvar::wait", ConcurrencyPrimitive::Condvar, ConcurrencyOperation::CondvarWait),
    (
        "std::sync::Condvar::notify_one",
        ConcurrencyPrimitive::Condvar,
        ConcurrencyOperation::CondvarNotify,
    ),
    (
        "std::sync::Condvar::notify_all",
        ConcurrencyPrimitive::Condvar,
        ConcurrencyOperation::CondvarNotify,
    ),
    // std::sync::atomic
    (
        "std::sync::atomic::AtomicBool::load",
        ConcurrencyPrimitive::Atomic,
        ConcurrencyOperation::AtomicLoad,
    ),
    (
        "std::sync::atomic::AtomicBool::store",
        ConcurrencyPrimitive::Atomic,
        ConcurrencyOperation::AtomicStore,
    ),
    (
        "std::sync::atomic::AtomicUsize::load",
        ConcurrencyPrimitive::Atomic,
        ConcurrencyOperation::AtomicLoad,
    ),
    (
        "std::sync::atomic::AtomicUsize::store",
        ConcurrencyPrimitive::Atomic,
        ConcurrencyOperation::AtomicStore,
    ),
    (
        "std::sync::atomic::AtomicUsize::compare_exchange",
        ConcurrencyPrimitive::Atomic,
        ConcurrencyOperation::AtomicCas,
    ),
    ("std::sync::atomic::fence", ConcurrencyPrimitive::Atomic, ConcurrencyOperation::AtomicFence),
    // tokio::sync::Mutex
    ("tokio::sync::Mutex::lock", ConcurrencyPrimitive::Mutex, ConcurrencyOperation::Lock),
    ("tokio::sync::Mutex::try_lock", ConcurrencyPrimitive::Mutex, ConcurrencyOperation::TryLock),
    // tokio::sync::RwLock
    ("tokio::sync::RwLock::read", ConcurrencyPrimitive::RwLock, ConcurrencyOperation::ReadLock),
    ("tokio::sync::RwLock::write", ConcurrencyPrimitive::RwLock, ConcurrencyOperation::Lock),
    // tokio::sync::Semaphore
    (
        "tokio::sync::Semaphore::acquire",
        ConcurrencyPrimitive::Semaphore,
        ConcurrencyOperation::SemaphoreAcquire,
    ),
    // tokio::sync::Notify
    (
        "tokio::sync::Notify::notify_one",
        ConcurrencyPrimitive::Notify,
        ConcurrencyOperation::NotifySignal,
    ),
    (
        "tokio::sync::Notify::notify_waiters",
        ConcurrencyPrimitive::Notify,
        ConcurrencyOperation::NotifySignal,
    ),
    (
        "tokio::sync::Notify::notified",
        ConcurrencyPrimitive::Notify,
        ConcurrencyOperation::NotifyWait,
    ),
    // tokio::spawn
    ("tokio::task::spawn", ConcurrencyPrimitive::AsyncSpawn, ConcurrencyOperation::Spawn),
    ("tokio::spawn", ConcurrencyPrimitive::AsyncSpawn, ConcurrencyOperation::Spawn),
    // crossbeam channels
    (
        "crossbeam::channel::bounded",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::ChannelCreate,
    ),
    (
        "crossbeam::channel::unbounded",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::ChannelCreate,
    ),
    ("crossbeam::channel::Sender::send", ConcurrencyPrimitive::Channel, ConcurrencyOperation::Send),
    (
        "crossbeam::channel::Receiver::recv",
        ConcurrencyPrimitive::Channel,
        ConcurrencyOperation::Recv,
    ),
    // std::thread::spawn
    ("std::thread::spawn", ConcurrencyPrimitive::AsyncSpawn, ConcurrencyOperation::Spawn),
];

// ---------------------------------------------------------------------------
// Phase 2: Thread model types for happens-before analysis
// ---------------------------------------------------------------------------

/// A thread spawn site detected in MIR.
///
/// Represents a call to `std::thread::spawn` (or builder pattern) with enough
/// context to build happens-before edges between the spawning thread and the
/// spawned thread.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThreadSpawnSite {
    /// The def_path of the function containing the spawn call.
    pub caller_function: String,
    /// MIR block where the spawn call lives.
    pub block: BlockId,
    /// The function or closure passed to spawn, if resolvable.
    pub spawn_target: SpawnTarget,
    /// MIR local that receives the JoinHandle.
    pub join_handle_local: Option<usize>,
    /// Source location.
    pub span: SourceSpan,
}

/// What was passed to `thread::spawn`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpawnTarget {
    /// A closure literal (inline closure at the spawn site).
    Closure {
        /// Captured variables (MIR local indices in the enclosing function).
        captures: Vec<usize>,
    },
    /// A named function item (e.g., `thread::spawn(worker_fn)`).
    NamedFunction {
        /// The def_path of the function.
        def_path: String,
    },
    /// Could not resolve the spawn target (function pointer, trait object, etc.).
    Unknown,
}

/// A join site where a JoinHandle is consumed.
///
/// Tracks the `JoinHandle::join()` call that establishes the HB edge
/// from the spawned thread's last operation back to the joining thread.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinSite {
    /// The def_path of the function containing the join call.
    pub caller_function: String,
    /// MIR block where the join call lives.
    pub block: BlockId,
    /// MIR local holding the JoinHandle being joined.
    pub handle_local: usize,
    /// Source location.
    pub span: SourceSpan,
}

/// Canonical identity for a memory location accessed by multiple threads.
///
/// Used to determine whether two accesses in different threads refer to the
/// same memory location. Conservative: unknown locations may-alias with
/// anything of the same type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryLocationId {
    /// A global `static` variable, identified by its def_path.
    Global { def_path: String },
    /// A direct `&AtomicT` function parameter.
    Parameter { function: String, param_index: usize },
    /// An `Arc<T>` captured by a spawn closure, traced back to its allocation.
    ArcCapture { source_def_path: String },
    /// Could not determine the memory location identity.
    Unknown { description: String },
}

impl std::fmt::Display for MemoryLocationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemoryLocationId::Global { def_path } => write!(f, "global:{def_path}"),
            MemoryLocationId::Parameter { function, param_index } => {
                write!(f, "param:{function}[{param_index}]")
            }
            MemoryLocationId::ArcCapture { source_def_path } => {
                write!(f, "arc:{source_def_path}")
            }
            MemoryLocationId::Unknown { description } => write!(f, "unknown:{description}"),
        }
    }
}

/// The kind of happens-before edge in the concurrency graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HappensBeforeEdgeKind {
    /// Intra-thread program order: sequential statements within one thread.
    ProgramOrder,
    /// Thread spawn: the spawn call HB the first operation of the child thread.
    Spawn,
    /// Thread join: the last operation of the child thread HB the join return.
    Join,
    /// Release-acquire synchronization on an atomic variable.
    SyncWith,
    /// Lock acquisition after an unlock on the same mutex.
    LockUnlock,
    /// Atomic fence-based synchronization.
    Fence,
}

/// A program point: a specific location in a specific function and thread.
///
/// This is the node type in the happens-before graph. Two program points
/// are ordered if there exists a path of HB edges between them.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConcurrencyPoint {
    /// The function containing this point.
    pub function: String,
    /// The basic block within the function.
    pub block: BlockId,
    /// The thread this point executes in (empty string = main thread).
    pub thread_id: String,
}

impl ConcurrencyPoint {
    /// Create a new program point.
    #[must_use]
    pub fn new(function: impl Into<String>, block: BlockId, thread_id: impl Into<String>) -> Self {
        Self { function: function.into(), block, thread_id: thread_id.into() }
    }
}

impl std::fmt::Display for ConcurrencyPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::bb{}@{}", self.function, self.block.0, self.thread_id)
    }
}

/// Thread spawn detection patterns for MIR Call terminators.
///
/// These patterns identify thread creation and join operations in addition
/// to the existing concurrency patterns. Used by the HB graph builder to
/// establish spawn/join HB edges.
pub const THREAD_SPAWN_PATTERNS: &[&str] = &["std::thread::spawn", "std::thread::Builder::spawn"];

/// Thread join detection patterns.
pub const THREAD_JOIN_PATTERNS: &[&str] = &["std::thread::JoinHandle::join"];

/// Rayon parallel patterns (for future extension).
pub const RAYON_SPAWN_PATTERNS: &[&str] = &["rayon::spawn", "rayon::scope", "rayon::join"];

/// Tokio task spawn patterns (for future extension).
pub const TOKIO_SPAWN_PATTERNS: &[&str] =
    &["tokio::spawn", "tokio::task::spawn", "tokio::task::spawn_blocking"];

/// Check whether a MIR Call func path is a thread spawn operation.
///
/// Strips generic parameters before matching.
#[must_use]
pub fn is_thread_spawn(func_path: &str) -> bool {
    let normalized = strip_generics(func_path);
    THREAD_SPAWN_PATTERNS.iter().any(|p| normalized.contains(p))
}

/// Check whether a MIR Call func path is a thread join operation.
///
/// Strips generic parameters before matching.
#[must_use]
pub fn is_thread_join(func_path: &str) -> bool {
    let normalized = strip_generics(func_path);
    THREAD_JOIN_PATTERNS.iter().any(|p| normalized.contains(p))
}

/// Detect all thread spawn sites in a VerifiableFunction.
///
/// Walks all basic blocks, inspects Call terminators, and identifies calls
/// to `std::thread::spawn` and similar patterns. For each spawn site,
/// attempts to resolve the closure or function being spawned.
pub fn detect_thread_spawns(func: &crate::VerifiableFunction) -> Vec<ThreadSpawnSite> {
    let mut sites = Vec::new();

    for block in &func.body.blocks {
        if let crate::Terminator::Call { func: func_name, args, dest, span, .. } = &block.terminator
            && is_thread_spawn(func_name)
        {
            let spawn_target = resolve_spawn_target(args);
            sites.push(ThreadSpawnSite {
                caller_function: func.def_path.clone(),
                block: block.id,
                spawn_target,
                join_handle_local: Some(dest.local),
                span: span.clone(),
            });
        }
    }

    sites
}

/// Detect all thread join sites in a VerifiableFunction.
pub fn detect_thread_joins(func: &crate::VerifiableFunction) -> Vec<JoinSite> {
    let mut sites = Vec::new();

    for block in &func.body.blocks {
        if let crate::Terminator::Call { func: func_name, args, span, .. } = &block.terminator
            && is_thread_join(func_name)
        {
            // The first argument to JoinHandle::join is the handle itself.
            let handle_local = args
                .first()
                .and_then(|arg| match arg {
                    crate::Operand::Copy(place) | crate::Operand::Move(place) => Some(place.local),
                    _ => None,
                })
                .unwrap_or(0);

            sites.push(JoinSite {
                caller_function: func.def_path.clone(),
                block: block.id,
                handle_local,
                span: span.clone(),
            });
        }
    }

    sites
}

/// Attempt to resolve what function/closure is being passed to spawn.
fn resolve_spawn_target(args: &[crate::Operand]) -> SpawnTarget {
    // The first argument to std::thread::spawn is the closure/fn.
    match args.first() {
        Some(crate::Operand::Copy(place) | crate::Operand::Move(place)) => {
            // A simple local — likely a closure capture or function item.
            // Without type info, we record it as a closure with the local as a capture.
            SpawnTarget::Closure { captures: vec![place.local] }
        }
        _ => SpawnTarget::Unknown,
    }
}

// strip_generics: consolidated into trust-types::utils
use crate::utils::strip_generics;

/// Match a MIR Call func path against known concurrency patterns.
///
/// Returns the matching (primitive, operation) if found. Uses longest-match
/// semantics when multiple patterns match the same call path.
/// Strips generic parameters before matching so that
/// `std::sync::Mutex::<T>::lock` matches pattern `std::sync::Mutex::lock`.
pub fn match_concurrency_call(
    func_path: &str,
) -> Option<(ConcurrencyPrimitive, ConcurrencyOperation)> {
    let normalized = strip_generics(func_path);
    let mut best_match: Option<(usize, ConcurrencyPrimitive, ConcurrencyOperation)> = None;

    for &(pattern, primitive, operation) in CONCURRENCY_PATTERNS {
        if normalized.contains(pattern) {
            let len = pattern.len();
            if best_match.as_ref().is_none_or(|(best_len, _, _)| len > *best_len) {
                best_match = Some((len, primitive, operation));
            }
        }
    }

    best_match.map(|(_, primitive, operation)| (primitive, operation))
}

/// Extract a concurrency model from a VerifiableFunction.
///
/// Walks all basic blocks, inspects Call terminators, and matches their
/// func path against known concurrency patterns. Builds a ConcurrencyModel
/// with shared resources and events.
///
/// This operates purely on trust-types data (no rustc dependency), so it
/// can be called both during MIR extraction and in downstream analysis.
pub fn extract_concurrency_model(func: &crate::VerifiableFunction) -> ConcurrencyModel {
    let mut model = ConcurrencyModel::new(&func.def_path);
    let mut resource_counter: FxHashMap<ConcurrencyPrimitive, usize> = FxHashMap::default();

    for block in &func.body.blocks {
        if let crate::Terminator::Call { func: func_name, dest, span, .. } = &block.terminator
            && let Some((primitive, operation)) = match_concurrency_call(func_name)
        {
            // Generate a resource ID from the destination place and primitive type.
            // For channel create operations, use the dest local as the resource.
            // For lock/send/recv, use the first arg (the self receiver) local.
            let resource_key = format!("{:?}_{}", primitive, dest.local);

            let count = resource_counter.entry(primitive).or_insert(0);
            let resource_id = ResourceId(resource_key.clone());

            model.add_resource(SharedResource {
                id: resource_id.clone(),
                primitive,
                name: None, // Name resolution requires debug info lookup
                guarded_type: None,
            });

            model.add_event(ConcurrencyEvent {
                operation,
                resource_id,
                block: block.id,
                span: span.clone(),
                call_path: func_name.clone(),
            });

            *count += 1;
        }
    }

    model
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match_mutex_lock() {
        let result = match_concurrency_call("std::sync::Mutex::<T>::lock");
        assert!(result.is_some());
        let (prim, op) = result.unwrap();
        assert_eq!(prim, ConcurrencyPrimitive::Mutex);
        assert_eq!(op, ConcurrencyOperation::Lock);
    }

    #[test]
    fn test_match_mutex_try_lock() {
        // try_lock should match TryLock, not Lock (longest match)
        let result = match_concurrency_call("std::sync::Mutex::<T>::try_lock");
        assert!(result.is_some());
        let (prim, op) = result.unwrap();
        assert_eq!(prim, ConcurrencyPrimitive::Mutex);
        assert_eq!(op, ConcurrencyOperation::TryLock);
    }

    #[test]
    fn test_match_rwlock_read() {
        let result = match_concurrency_call("std::sync::RwLock::<T>::read");
        assert!(result.is_some());
        let (prim, op) = result.unwrap();
        assert_eq!(prim, ConcurrencyPrimitive::RwLock);
        assert_eq!(op, ConcurrencyOperation::ReadLock);
    }

    #[test]
    fn test_match_rwlock_write() {
        let result = match_concurrency_call("std::sync::RwLock::<T>::write");
        assert!(result.is_some());
        let (prim, op) = result.unwrap();
        assert_eq!(prim, ConcurrencyPrimitive::RwLock);
        assert_eq!(op, ConcurrencyOperation::Lock);
    }

    #[test]
    fn test_match_channel_send_recv() {
        let send = match_concurrency_call("std::sync::mpsc::Sender::<T>::send");
        assert!(send.is_some());
        assert_eq!(send.unwrap().1, ConcurrencyOperation::Send);

        let recv = match_concurrency_call("std::sync::mpsc::Receiver::<T>::recv");
        assert!(recv.is_some());
        assert_eq!(recv.unwrap().1, ConcurrencyOperation::Recv);
    }

    #[test]
    fn test_match_channel_create() {
        let result = match_concurrency_call("std::sync::mpsc::channel");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, ConcurrencyPrimitive::Channel);
        assert_eq!(result.unwrap().1, ConcurrencyOperation::ChannelCreate);
    }

    #[test]
    fn test_match_condvar() {
        let wait = match_concurrency_call("std::sync::Condvar::wait");
        assert!(wait.is_some());
        assert_eq!(wait.unwrap().1, ConcurrencyOperation::CondvarWait);

        let notify = match_concurrency_call("std::sync::Condvar::notify_one");
        assert!(notify.is_some());
        assert_eq!(notify.unwrap().1, ConcurrencyOperation::CondvarNotify);
    }

    #[test]
    fn test_match_atomic_operations() {
        let load = match_concurrency_call("std::sync::atomic::AtomicUsize::load");
        assert!(load.is_some());
        assert_eq!(load.unwrap().0, ConcurrencyPrimitive::Atomic);
        assert_eq!(load.unwrap().1, ConcurrencyOperation::AtomicLoad);

        let cas = match_concurrency_call("std::sync::atomic::AtomicUsize::compare_exchange");
        assert!(cas.is_some());
        assert_eq!(cas.unwrap().1, ConcurrencyOperation::AtomicCas);

        let fence = match_concurrency_call("std::sync::atomic::fence");
        assert!(fence.is_some());
        assert_eq!(fence.unwrap().1, ConcurrencyOperation::AtomicFence);
    }

    #[test]
    fn test_match_tokio_mutex() {
        let result = match_concurrency_call("tokio::sync::Mutex::<T>::lock");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, ConcurrencyPrimitive::Mutex);
    }

    #[test]
    fn test_match_tokio_rwlock() {
        let read = match_concurrency_call("tokio::sync::RwLock::<T>::read");
        assert!(read.is_some());
        assert_eq!(read.unwrap().0, ConcurrencyPrimitive::RwLock);
        assert_eq!(read.unwrap().1, ConcurrencyOperation::ReadLock);
    }

    #[test]
    fn test_match_tokio_semaphore() {
        let result = match_concurrency_call("tokio::sync::Semaphore::acquire");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, ConcurrencyPrimitive::Semaphore);
        assert_eq!(result.unwrap().1, ConcurrencyOperation::SemaphoreAcquire);
    }

    #[test]
    fn test_match_tokio_notify() {
        let signal = match_concurrency_call("tokio::sync::Notify::notify_one");
        assert!(signal.is_some());
        assert_eq!(signal.unwrap().0, ConcurrencyPrimitive::Notify);
        assert_eq!(signal.unwrap().1, ConcurrencyOperation::NotifySignal);

        let wait = match_concurrency_call("tokio::sync::Notify::notified");
        assert!(wait.is_some());
        assert_eq!(wait.unwrap().1, ConcurrencyOperation::NotifyWait);
    }

    #[test]
    fn test_match_tokio_spawn() {
        let result = match_concurrency_call("tokio::task::spawn");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, ConcurrencyPrimitive::AsyncSpawn);
        assert_eq!(result.unwrap().1, ConcurrencyOperation::Spawn);
    }

    #[test]
    fn test_match_crossbeam() {
        let bounded = match_concurrency_call("crossbeam::channel::bounded");
        assert!(bounded.is_some());
        assert_eq!(bounded.unwrap().0, ConcurrencyPrimitive::Channel);
        assert_eq!(bounded.unwrap().1, ConcurrencyOperation::ChannelCreate);

        let send = match_concurrency_call("crossbeam::channel::Sender::send");
        assert!(send.is_some());
        assert_eq!(send.unwrap().1, ConcurrencyOperation::Send);
    }

    #[test]
    fn test_match_thread_spawn() {
        let result = match_concurrency_call("std::thread::spawn");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, ConcurrencyPrimitive::AsyncSpawn);
        assert_eq!(result.unwrap().1, ConcurrencyOperation::Spawn);
    }

    #[test]
    fn test_no_match_for_unrelated_calls() {
        assert!(match_concurrency_call("std::vec::Vec::push").is_none());
        assert!(match_concurrency_call("my_crate::lock_something").is_none());
        assert!(match_concurrency_call("HashMap::insert").is_none());
    }

    #[test]
    fn test_concurrency_model_empty() {
        let model = ConcurrencyModel::new("test_fn");
        assert!(model.is_empty());
        assert_eq!(model.function, "test_fn");
    }

    #[test]
    fn test_concurrency_model_add_resource_dedup() {
        let mut model = ConcurrencyModel::new("test_fn");
        let resource = SharedResource {
            id: ResourceId("mutex_1".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: Some("data".into()),
            guarded_type: Some("Vec<i32>".into()),
        };

        model.add_resource(resource.clone());
        model.add_resource(resource);
        assert_eq!(model.resources.len(), 1);
    }

    #[test]
    fn test_lock_order_violation_detection() {
        let mut model = ConcurrencyModel::new("test_fn");
        model.add_resource(SharedResource {
            id: ResourceId("lock_a".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: Some("a".into()),
            guarded_type: None,
        });
        model.add_resource(SharedResource {
            id: ResourceId("lock_b".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: Some("b".into()),
            guarded_type: None,
        });

        // Path 1: lock A then lock B
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("lock_a".into()),
            block: BlockId(0),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("lock_b".into()),
            block: BlockId(1),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });
        // Path 2: lock B then lock A (reversed order)
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("lock_b".into()),
            block: BlockId(2),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("lock_a".into()),
            block: BlockId(3),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });

        let violations = model.detect_lock_order_violations();
        assert!(!violations.is_empty(), "should detect lock ordering violation");
        assert_eq!(violations[0].resource_a, ResourceId("lock_b".into()));
        assert_eq!(violations[0].resource_b, ResourceId("lock_a".into()));
    }

    #[test]
    fn test_no_lock_order_violation_consistent() {
        let mut model = ConcurrencyModel::new("test_fn");
        model.add_resource(SharedResource {
            id: ResourceId("lock_a".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: None,
            guarded_type: None,
        });
        model.add_resource(SharedResource {
            id: ResourceId("lock_b".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: None,
            guarded_type: None,
        });

        // Consistent order: always A then B
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("lock_a".into()),
            block: BlockId(0),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("lock_b".into()),
            block: BlockId(1),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });

        let violations = model.detect_lock_order_violations();
        assert!(violations.is_empty(), "consistent ordering should have no violations");
    }

    #[test]
    fn test_resources_of_type() {
        let mut model = ConcurrencyModel::new("test_fn");
        model.add_resource(SharedResource {
            id: ResourceId("m1".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: None,
            guarded_type: None,
        });
        model.add_resource(SharedResource {
            id: ResourceId("ch1".into()),
            primitive: ConcurrencyPrimitive::Channel,
            name: None,
            guarded_type: None,
        });
        model.add_resource(SharedResource {
            id: ResourceId("m2".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: None,
            guarded_type: None,
        });

        assert_eq!(model.resources_of_type(ConcurrencyPrimitive::Mutex).len(), 2);
        assert_eq!(model.resources_of_type(ConcurrencyPrimitive::Channel).len(), 1);
        assert_eq!(model.resources_of_type(ConcurrencyPrimitive::RwLock).len(), 0);
    }

    #[test]
    fn test_events_for_resource() {
        let mut model = ConcurrencyModel::new("test_fn");
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("m1".into()),
            block: BlockId(0),
            span: SourceSpan::default(),
            call_path: "lock".into(),
        });
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Send,
            resource_id: ResourceId("ch1".into()),
            block: BlockId(1),
            span: SourceSpan::default(),
            call_path: "send".into(),
        });
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Unlock,
            resource_id: ResourceId("m1".into()),
            block: BlockId(2),
            span: SourceSpan::default(),
            call_path: "unlock".into(),
        });

        assert_eq!(model.events_for_resource(&ResourceId("m1".into())).len(), 2);
        assert_eq!(model.events_for_resource(&ResourceId("ch1".into())).len(), 1);
    }

    #[test]
    fn test_tla_plus_generation_mutex() {
        let mut model = ConcurrencyModel::new("my_module::critical_section");
        model.add_resource(SharedResource {
            id: ResourceId("data_lock".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: Some("data_lock".into()),
            guarded_type: Some("Vec<i32>".into()),
        });

        let tla = model.to_tla_plus();
        assert!(tla.contains("MODULE my_module__critical_section"));
        assert!(tla.contains("held_data_lock"));
        assert!(tla.contains("Init =="));
        assert!(tla.contains("held_data_lock = \"none\""));
        assert!(tla.contains("Lock_data_lock"));
        assert!(tla.contains("Unlock_data_lock"));
        assert!(tla.contains("DeadlockFreedom"));
        assert!(tla.contains("MutualExclusion_data_lock"));
        assert!(tla.contains("Spec =="));
        assert!(tla.contains("===="));
    }

    #[test]
    fn test_tla_plus_generation_channel() {
        let mut model = ConcurrencyModel::new("producer_consumer");
        model.add_resource(SharedResource {
            id: ResourceId("work_queue".into()),
            primitive: ConcurrencyPrimitive::Channel,
            name: Some("work_queue".into()),
            guarded_type: None,
        });

        let tla = model.to_tla_plus();
        assert!(tla.contains("buffer_work_queue"));
        assert!(tla.contains("Send_work_queue"));
        assert!(tla.contains("Recv_work_queue"));
        assert!(tla.contains("Append(buffer_work_queue, msg)"));
        assert!(tla.contains("Tail(buffer_work_queue)"));
        assert!(tla.contains("ChannelLiveness_work_queue"));
    }

    #[test]
    fn test_tla_plus_generation_rwlock() {
        let mut model = ConcurrencyModel::new("rw_test");
        model.add_resource(SharedResource {
            id: ResourceId("cache".into()),
            primitive: ConcurrencyPrimitive::RwLock,
            name: Some("cache".into()),
            guarded_type: None,
        });

        let tla = model.to_tla_plus();
        assert!(tla.contains("readers_cache"));
        assert!(tla.contains("writer_cache"));
        assert!(tla.contains("ReadLock_cache"));
        assert!(tla.contains("WriteLock_cache"));
    }

    #[test]
    fn test_tla_plus_generation_empty() {
        let model = ConcurrencyModel::new("empty_fn");
        let tla = model.to_tla_plus();
        assert!(tla.contains("MODULE empty_fn"));
        assert!(tla.contains("UNCHANGED vars"));
        assert!(tla.contains("===="));
    }

    #[test]
    fn test_sanitize_tla_name() {
        assert_eq!(sanitize_tla_name("my_module::func"), "my_module__func");
        assert_eq!(sanitize_tla_name("simple"), "simple");
        assert_eq!(sanitize_tla_name("a::b::c"), "a__b__c");
    }

    #[test]
    fn test_serialization_roundtrip() {
        let mut model = ConcurrencyModel::new("test_fn");
        model.add_resource(SharedResource {
            id: ResourceId("m".into()),
            primitive: ConcurrencyPrimitive::Mutex,
            name: Some("m".into()),
            guarded_type: None,
        });
        model.add_event(ConcurrencyEvent {
            operation: ConcurrencyOperation::Lock,
            resource_id: ResourceId("m".into()),
            block: BlockId(0),
            span: SourceSpan::default(),
            call_path: "std::sync::Mutex::lock".into(),
        });

        let json = serde_json::to_string(&model).expect("serialize");
        let round: ConcurrencyModel = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.function, "test_fn");
        assert_eq!(round.resources.len(), 1);
        assert_eq!(round.events.len(), 1);
    }

    /// Build a mock VerifiableFunction with concurrency calls for testing.
    fn make_concurrent_function() -> crate::VerifiableFunction {
        use crate::*;
        VerifiableFunction {
            name: "transfer".to_string(),
            def_path: "bank::transfer".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None }, // return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("amount".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("guard_a".into()) }, // lock result
                    LocalDecl { index: 3, ty: Ty::Unit, name: Some("guard_b".into()) }, // lock result
                    LocalDecl { index: 4, ty: Ty::Unit, name: Some("tx".into()) },      // channel
                ],
                blocks: vec![
                    // bb0: lock mutex A
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "std::sync::Mutex::<Account>::lock".into(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "bank.rs".into(),
                                line_start: 10,
                                col_start: 4,
                                line_end: 10,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    // bb1: lock mutex B
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "std::sync::Mutex::<Account>::lock".into(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(3),
                            target: Some(BlockId(2)),
                            span: SourceSpan {
                                file: "bank.rs".into(),
                                line_start: 11,
                                col_start: 4,
                                line_end: 11,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    // bb2: send on channel
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "std::sync::mpsc::Sender::<TransferEvent>::send".into(),
                            args: vec![Operand::Copy(Place::local(4))],
                            dest: Place::local(0),
                            target: Some(BlockId(3)),
                            span: SourceSpan {
                                file: "bank.rs".into(),
                                line_start: 15,
                                col_start: 4,
                                line_end: 15,
                                col_end: 40,
                            },
                            atomic: None,
                        },
                    },
                    // bb3: return
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_extract_concurrency_model_from_function() {
        let func = make_concurrent_function();
        let model = extract_concurrency_model(&func);

        assert_eq!(model.function, "bank::transfer");
        assert!(!model.is_empty());

        // Should detect 2 mutex locks and 1 channel send
        assert_eq!(model.events.len(), 3);

        let mutex_events: Vec<_> =
            model.events.iter().filter(|e| e.operation == ConcurrencyOperation::Lock).collect();
        assert_eq!(mutex_events.len(), 2, "should detect two mutex lock operations");

        let send_events: Vec<_> =
            model.events.iter().filter(|e| e.operation == ConcurrencyOperation::Send).collect();
        assert_eq!(send_events.len(), 1, "should detect one channel send");

        // Should have resources for mutex and channel
        let mutex_resources = model.resources_of_type(ConcurrencyPrimitive::Mutex);
        assert!(!mutex_resources.is_empty(), "should have mutex resources");

        let channel_resources = model.resources_of_type(ConcurrencyPrimitive::Channel);
        assert!(!channel_resources.is_empty(), "should have channel resources");
    }

    #[test]
    fn test_extract_concurrency_model_generates_tla() {
        let func = make_concurrent_function();
        let model = extract_concurrency_model(&func);
        let tla = model.to_tla_plus();

        assert!(tla.contains("MODULE bank__transfer"), "TLA+ should use sanitized function name");
        assert!(tla.contains("Init =="), "TLA+ should have Init predicate");
        assert!(tla.contains("Next =="), "TLA+ should have Next relation");
        assert!(tla.contains("DeadlockFreedom"), "TLA+ should have deadlock freedom property");
        assert!(tla.contains("Spec =="), "TLA+ should have Spec");
        assert!(tla.contains("===="), "TLA+ should have module end");
    }

    #[test]
    fn test_extract_concurrency_model_empty_function() {
        use crate::*;
        let func = VerifiableFunction {
            name: "simple_add".to_string(),
            def_path: "math::simple_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = extract_concurrency_model(&func);
        assert!(model.is_empty(), "non-concurrent function should produce empty model");
        assert!(model.resources.is_empty());
    }

    #[test]
    fn test_extract_tokio_async_primitives() {
        use crate::*;
        let func = VerifiableFunction {
            name: "async_handler".to_string(),
            def_path: "server::async_handler".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("guard".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("task".into()) },
                    LocalDecl { index: 3, ty: Ty::Unit, name: Some("sem".into()) },
                ],
                blocks: vec![
                    // tokio mutex lock
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "tokio::sync::Mutex::<State>::lock".into(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // tokio::spawn
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "tokio::task::spawn".into(),
                            args: vec![],
                            dest: Place::local(2),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // tokio semaphore acquire
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "tokio::sync::Semaphore::acquire".into(),
                            args: vec![],
                            dest: Place::local(3),
                            target: Some(BlockId(3)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = extract_concurrency_model(&func);
        assert_eq!(model.events.len(), 3);

        // Verify tokio mutex detected
        assert!(model.events.iter().any(|e| e.operation == ConcurrencyOperation::Lock));
        // Verify spawn detected
        assert!(model.events.iter().any(|e| e.operation == ConcurrencyOperation::Spawn));
        // Verify semaphore detected
        assert!(model.events.iter().any(|e| e.operation == ConcurrencyOperation::SemaphoreAcquire));
    }

    #[test]
    fn test_strip_generics() {
        assert_eq!(strip_generics("std::sync::Mutex::<T>::lock"), "std::sync::Mutex::lock");
        assert_eq!(strip_generics("HashMap::<K, V>::get"), "HashMap::get");
        assert_eq!(strip_generics("simple::path"), "simple::path");
        assert_eq!(strip_generics("Outer::<Inner::<T>>::method"), "Outer::method");
    }

    // -----------------------------------------------------------------------
    // Phase 2: Thread model types tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_thread_spawn() {
        assert!(is_thread_spawn("std::thread::spawn"));
        assert!(is_thread_spawn("std::thread::spawn::<closure>"));
        assert!(is_thread_spawn("std::thread::Builder::spawn"));
        assert!(!is_thread_spawn("tokio::spawn"));
        assert!(!is_thread_spawn("std::sync::Mutex::lock"));
        assert!(!is_thread_spawn("my_module::spawn_worker"));
    }

    #[test]
    fn test_is_thread_join() {
        assert!(is_thread_join("std::thread::JoinHandle::join"));
        assert!(is_thread_join("std::thread::JoinHandle::<T>::join"));
        assert!(!is_thread_join("std::thread::spawn"));
        assert!(!is_thread_join("tokio::task::JoinHandle::join"));
    }

    #[test]
    fn test_detect_thread_spawns() {
        use crate::*;
        let func = VerifiableFunction {
            name: "spawner".to_string(),
            def_path: "my_mod::spawner".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("closure".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("handle".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "std::thread::spawn::<closure>".into(),
                            args: vec![Operand::Move(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "main.rs".into(),
                                line_start: 5,
                                col_start: 4,
                                line_end: 5,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let spawns = detect_thread_spawns(&func);
        assert_eq!(spawns.len(), 1);
        assert_eq!(spawns[0].caller_function, "my_mod::spawner");
        assert_eq!(spawns[0].block, BlockId(0));
        assert_eq!(spawns[0].join_handle_local, Some(2));
        assert!(
            matches!(spawns[0].spawn_target, SpawnTarget::Closure { ref captures } if captures == &[1])
        );
    }

    #[test]
    fn test_detect_thread_joins() {
        use crate::*;
        let func = VerifiableFunction {
            name: "joiner".to_string(),
            def_path: "my_mod::joiner".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("handle".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("result".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                            func: "std::thread::JoinHandle::<()>::join".into(),
                            args: vec![Operand::Move(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "main.rs".into(),
                                line_start: 10,
                                col_start: 4,
                                line_end: 10,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let joins = detect_thread_joins(&func);
        assert_eq!(joins.len(), 1);
        assert_eq!(joins[0].caller_function, "my_mod::joiner");
        assert_eq!(joins[0].block, BlockId(0));
        assert_eq!(joins[0].handle_local, 1);
    }

    #[test]
    fn test_detect_no_spawns_in_regular_function() {
        use crate::*;
        let func = VerifiableFunction {
            name: "add".to_string(),
            def_path: "math::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        assert!(detect_thread_spawns(&func).is_empty());
        assert!(detect_thread_joins(&func).is_empty());
    }

    #[test]
    fn test_memory_location_id_display() {
        let global = MemoryLocationId::Global { def_path: "my_mod::COUNTER".to_string() };
        assert_eq!(global.to_string(), "global:my_mod::COUNTER");

        let param = MemoryLocationId::Parameter { function: "worker".to_string(), param_index: 0 };
        assert_eq!(param.to_string(), "param:worker[0]");

        let arc = MemoryLocationId::ArcCapture { source_def_path: "main::data".to_string() };
        assert_eq!(arc.to_string(), "arc:main::data");

        let unknown = MemoryLocationId::Unknown { description: "indirect".to_string() };
        assert_eq!(unknown.to_string(), "unknown:indirect");
    }

    #[test]
    fn test_memory_location_id_eq_hash() {
        use crate::fx::FxHashSet;
        let a = MemoryLocationId::Global { def_path: "x".to_string() };
        let b = MemoryLocationId::Global { def_path: "x".to_string() };
        let c = MemoryLocationId::Global { def_path: "y".to_string() };

        assert_eq!(a, b);
        assert_ne!(a, c);

        let mut set = FxHashSet::default();
        set.insert(a.clone());
        set.insert(b);
        assert_eq!(set.len(), 1);
        set.insert(c);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_program_point_display() {
        let pp = ConcurrencyPoint::new("my_fn", BlockId(3), "thread_1");
        assert_eq!(pp.to_string(), "my_fn::bb3@thread_1");
    }

    #[test]
    fn test_happens_before_edge_kind_values() {
        // Ensure all variants are distinct
        let kinds = [
            HappensBeforeEdgeKind::ProgramOrder,
            HappensBeforeEdgeKind::Spawn,
            HappensBeforeEdgeKind::Join,
            HappensBeforeEdgeKind::SyncWith,
            HappensBeforeEdgeKind::LockUnlock,
            HappensBeforeEdgeKind::Fence,
        ];
        for (i, a) in kinds.iter().enumerate() {
            for (j, b) in kinds.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b);
                }
            }
        }
    }

    #[test]
    fn test_thread_spawn_site_serialization_roundtrip() {
        let site = ThreadSpawnSite {
            caller_function: "main::run".to_string(),
            block: BlockId(2),
            spawn_target: SpawnTarget::NamedFunction { def_path: "worker::process".to_string() },
            join_handle_local: Some(5),
            span: SourceSpan::default(),
        };

        let json = serde_json::to_string(&site).expect("serialize");
        let round: ThreadSpawnSite = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, site);
    }

    #[test]
    fn test_join_site_serialization_roundtrip() {
        let site = JoinSite {
            caller_function: "main::run".to_string(),
            block: BlockId(4),
            handle_local: 5,
            span: SourceSpan::default(),
        };

        let json = serde_json::to_string(&site).expect("serialize");
        let round: JoinSite = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, site);
    }

    #[test]
    fn test_spawn_target_variants() {
        let closure = SpawnTarget::Closure { captures: vec![1, 2, 3] };
        let named = SpawnTarget::NamedFunction { def_path: "worker".to_string() };
        let unknown = SpawnTarget::Unknown;

        assert_ne!(closure, named);
        assert_ne!(named, unknown);

        // Verify serialization roundtrip for all variants
        for target in [&closure, &named, &unknown] {
            let json = serde_json::to_string(target).expect("serialize");
            let round: SpawnTarget = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&round, target);
        }
    }
}
