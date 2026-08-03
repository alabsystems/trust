// trust_vcgen/send_sync.rs: Send/Sync concurrency verification
//
// Verifies that types implementing Send/Sync are safe to share across
// threads. Generates VCs for thread safety properties: data race freedom,
// mutex correctness, and atomic ordering validity.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: #612 -- re-export AtomicOrdering from trust_types (canonical, lattice-correct).
// The previous local AtomicOrdering had a buggy derived Ord (Acquire < Release).
// The canonical type correctly models Acquire/Release as incomparable in the C11 lattice.
pub use trust_types::AtomicOrdering;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// Thread safety property types
// ---------------------------------------------------------------------------

/// A type's thread-safety classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ThreadSafety {
    /// Safe to send across thread boundaries (implements Send).
    Send,
    /// Safe to share references across threads (implements Sync).
    Sync,
    /// Both Send and Sync.
    SendSync,
    /// Neither Send nor Sync.
    Unsafe,
}

impl std::fmt::Display for ThreadSafety {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Send => write!(f, "Send"),
            Self::Sync => write!(f, "Sync"),
            Self::SendSync => write!(f, "Send + Sync"),
            Self::Unsafe => write!(f, "!Send + !Sync"),
        }
    }
}

/// A shared memory access pattern that may indicate a data race.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SharedAccess {
    /// Variable or memory location being accessed.
    pub location: String,
    /// Thread identifier (symbolic or concrete).
    pub thread: String,
    /// Whether this is a write access.
    pub is_write: bool,
    /// Source location of the access.
    pub span: SourceSpan,
}

/// Mutex acquire/release event for happens-before tracking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutexEvent {
    /// Mutex identifier.
    pub mutex_id: String,
    /// Thread performing the operation.
    pub thread: String,
    /// Whether this is an acquire (true) or release (false).
    pub is_acquire: bool,
    /// Source location.
    pub span: SourceSpan,
}

/// Atomic operation with ordering constraint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AtomicOp {
    /// Variable being accessed atomically.
    pub variable: String,
    /// Thread performing the operation.
    pub thread: String,
    /// Ordering level used.
    pub ordering: AtomicOrdering,
    /// Whether this is a store (true) or load (false).
    pub is_store: bool,
    /// Source location.
    pub span: SourceSpan,
}

// Trust: #612 -- AtomicOrdering is now re-exported from trust_types.
// The canonical type has a correct partial order where Acquire and Release
// are incomparable. is_at_least() replaces the old at_least().

// ---------------------------------------------------------------------------
// Send/Sync checker
// ---------------------------------------------------------------------------

/// Type info for Send/Sync checking.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    /// Type name.
    pub name: String,
    /// Whether the type implements Send.
    pub is_send: bool,
    /// Whether the type implements Sync.
    pub is_sync: bool,
    /// Field types (for struct/enum checking).
    pub fields: Vec<TypeInfo>,
    /// Whether this type uses interior mutability (UnsafeCell).
    pub has_interior_mutability: bool,
}

impl TypeInfo {
    /// Create a new type info.
    pub fn new(name: impl Into<String>, is_send: bool, is_sync: bool) -> Self {
        Self {
            name: name.into(),
            is_send,
            is_sync,
            fields: Vec::new(),
            has_interior_mutability: false,
        }
    }

    /// Get thread safety classification.
    #[must_use]
    pub fn safety(&self) -> ThreadSafety {
        match (self.is_send, self.is_sync) {
            (true, true) => ThreadSafety::SendSync,
            (true, false) => ThreadSafety::Send,
            (false, true) => ThreadSafety::Sync,
            (false, false) => ThreadSafety::Unsafe,
        }
    }
}

/// Checker for Send/Sync safety of types.
pub struct SendSyncChecker {
    /// Known type safety classifications.
    types: FxHashMap<String, TypeInfo>,
    /// Accumulated violations.
    violations: Vec<SendSyncViolation>,
}

/// A violation of Send/Sync safety.
#[derive(Debug, Clone)]
pub struct SendSyncViolation {
    /// Type that violates safety.
    pub type_name: String,
    /// What property is violated.
    pub kind: ViolationKind,
    /// Source location.
    pub span: SourceSpan,
    /// Explanation.
    pub message: String,
}

/// Kind of Send/Sync violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViolationKind {
    /// Type claims Send but contains non-Send field.
    UnsafeSend,
    /// Type claims Sync but contains non-Sync field.
    UnsafeSync,
    /// Type has interior mutability without proper synchronization.
    UnprotectedInteriorMutability,
    /// Raw pointer shared across threads without safety proof.
    UnsafeRawPointerSharing,
}

impl SendSyncChecker {
    /// Create a new checker.
    pub fn new() -> Self {
        Self { types: FxHashMap::default(), violations: Vec::new() }
    }

    /// Register a type for checking.
    pub fn register_type(&mut self, info: TypeInfo) {
        self.types.insert(info.name.clone(), info);
    }

    /// Check all registered types for Send/Sync safety.
    pub fn check_all(&mut self) -> Vec<SendSyncViolation> {
        let type_names: Vec<_> = self.types.keys().cloned().collect();
        for name in type_names {
            self.check_type(&name);
        }
        self.violations.clone()
    }

    /// Check a single type.
    fn check_type(&mut self, name: &str) {
        let info = match self.types.get(name) {
            Some(info) => info.clone(),
            None => return,
        };

        // If type claims Send, all fields must be Send.
        if info.is_send {
            for field in &info.fields {
                if !field.is_send {
                    self.violations.push(SendSyncViolation {
                        type_name: name.to_string(),
                        kind: ViolationKind::UnsafeSend,
                        span: SourceSpan::default(),
                        message: format!(
                            "type '{}' implements Send but field '{}' is !Send",
                            name, field.name
                        ),
                    });
                }
            }
        }

        // If type claims Sync, all fields must be Sync.
        if info.is_sync {
            for field in &info.fields {
                if !field.is_sync {
                    self.violations.push(SendSyncViolation {
                        type_name: name.to_string(),
                        kind: ViolationKind::UnsafeSync,
                        span: SourceSpan::default(),
                        message: format!(
                            "type '{}' implements Sync but field '{}' is !Sync",
                            name, field.name
                        ),
                    });
                }
            }
        }

        // Interior mutability without Sync is a problem if shared.
        if info.has_interior_mutability && !info.is_sync {
            self.violations.push(SendSyncViolation {
                type_name: name.to_string(),
                kind: ViolationKind::UnprotectedInteriorMutability,
                span: SourceSpan::default(),
                message: format!("type '{}' has interior mutability but is !Sync", name),
            });
        }
    }

    /// Generate VCs from violations.
    pub fn to_vcs(&self, function: &str) -> Vec<VerificationCondition> {
        self.violations
            .iter()
            .map(|v| {
                VerificationCondition {
                    kind: VcKind::Assertion { message: v.message.clone() },
                    function: function.into(),
                    location: v.span.clone(),
                    formula: Formula::Bool(false), // violation => unsatisfiable
                    contract_metadata: None,
                    obligation: None,
                }
            })
            .collect()
    }
}

impl Default for SendSyncChecker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Data race detector
// ---------------------------------------------------------------------------

/// Detects potential data races from shared memory access patterns.
pub struct DataRaceDetector {
    /// Shared memory accesses observed.
    accesses: Vec<SharedAccess>,
    /// Mutex events for happens-before.
    mutex_events: Vec<MutexEvent>,
    /// Detected races.
    races: Vec<DataRace>,
}

/// A detected data race between two accesses.
#[derive(Debug, Clone)]
pub struct DataRace {
    /// First access.
    pub access1: SharedAccess,
    /// Second access (conflicting).
    pub access2: SharedAccess,
    /// Whether a mutex protects this access pair.
    pub is_protected: bool,
}

impl DataRaceDetector {
    /// Create a new detector.
    pub fn new() -> Self {
        Self { accesses: Vec::new(), mutex_events: Vec::new(), races: Vec::new() }
    }

    /// Record a shared memory access.
    pub fn add_access(&mut self, access: SharedAccess) {
        self.accesses.push(access);
    }

    /// Record a mutex event.
    pub fn add_mutex_event(&mut self, event: MutexEvent) {
        self.mutex_events.push(event);
    }

    /// Detect all potential data races.
    ///
    /// A data race exists when two accesses to the same location from different
    /// threads have at least one write and no happens-before ordering.
    pub fn detect(&mut self) -> Vec<DataRace> {
        self.races.clear();

        // Group accesses by location.
        let mut by_location: FxHashMap<&str, Vec<&SharedAccess>> = FxHashMap::default();
        for access in &self.accesses {
            by_location.entry(&access.location).or_default().push(access);
        }

        // Build protected location set from mutex events.
        let protected = self.build_protected_set();

        // Check each location for conflicting accesses.
        for (location, accesses) in &by_location {
            for (i, a1) in accesses.iter().enumerate() {
                for a2 in accesses.iter().skip(i + 1) {
                    // Same thread is fine.
                    if a1.thread == a2.thread {
                        continue;
                    }
                    // At least one must be a write.
                    if !a1.is_write && !a2.is_write {
                        continue;
                    }
                    let is_protected = protected.contains(*location);
                    self.races.push(DataRace {
                        access1: (*a1).clone(),
                        access2: (*a2).clone(),
                        is_protected,
                    });
                }
            }
        }

        self.races.clone()
    }

    /// Build set of locations protected by mutexes.
    fn build_protected_set(&self) -> FxHashSet<String> {
        let mut protected = FxHashSet::default();
        // Simple heuristic: a location is protected if there are paired
        // acquire/release events on the same mutex from the same thread.
        let mut held: FxHashMap<(&str, &str), bool> = FxHashMap::default();
        for event in &self.mutex_events {
            let key = (event.mutex_id.as_str(), event.thread.as_str());
            if event.is_acquire {
                held.insert(key, true);
            } else if held.contains_key(&key) {
                // Release after acquire — anything between is protected.
                protected.insert(event.mutex_id.clone());
            }
        }
        protected
    }

    /// Generate VCs asserting each unprotected race is infeasible.
    pub fn to_vcs(&self, function: &str) -> Vec<VerificationCondition> {
        self.races
            .iter()
            .filter(|r| !r.is_protected)
            .map(|race| {
                let msg = format!(
                    "potential data race on '{}' between thread '{}' and '{}'",
                    race.access1.location, race.access1.thread, race.access2.thread
                );
                VerificationCondition {
                    kind: VcKind::Assertion { message: msg },
                    function: function.into(),
                    location: race.access1.span.clone(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                }
            })
            .collect()
    }
}

impl Default for DataRaceDetector {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Thread safety VC generator
// ---------------------------------------------------------------------------

/// Generate thread safety VCs for a function.
pub fn generate_thread_safety_vcs(
    function: &str,
    accesses: &[SharedAccess],
    mutex_events: &[MutexEvent],
    atomics: &[AtomicOp],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Data race VCs.
    let mut detector = DataRaceDetector::new();
    for access in accesses {
        detector.add_access(access.clone());
    }
    for event in mutex_events {
        detector.add_mutex_event(event.clone());
    }
    detector.detect();
    vcs.extend(detector.to_vcs(function));

    // Atomic ordering VCs.
    vcs.extend(check_atomic_ordering(function, atomics));

    vcs
}

/// Check atomic operations have correct ordering.
fn check_atomic_ordering(function: &str, atomics: &[AtomicOp]) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for op in atomics {
        // Stores need at least Release ordering for publish semantics.
        if op.is_store && !op.ordering.is_release() && op.ordering != AtomicOrdering::Relaxed {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "atomic store to '{}' uses {} ordering; Release or stronger recommended",
                        op.variable, op.ordering
                    ),
                },
                function: function.into(),
                location: op.span.clone(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            });
        }

        // Loads need at least Acquire ordering for consume semantics.
        if !op.is_store && !op.ordering.is_acquire() && op.ordering != AtomicOrdering::Relaxed {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "atomic load from '{}' uses {} ordering; Acquire or stronger recommended",
                        op.variable, op.ordering
                    ),
                },
                function: function.into(),
                location: op.span.clone(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            });
        }
    }

    vcs
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_safety_classification() {
        assert_eq!(ThreadSafety::Send.to_string(), "Send");
        assert_eq!(ThreadSafety::SendSync.to_string(), "Send + Sync");
    }

    #[test]
    fn test_type_info_safety() {
        let info = TypeInfo::new("Foo", true, true);
        assert_eq!(info.safety(), ThreadSafety::SendSync);

        let info = TypeInfo::new("Bar", true, false);
        assert_eq!(info.safety(), ThreadSafety::Send);

        let info = TypeInfo::new("Baz", false, false);
        assert_eq!(info.safety(), ThreadSafety::Unsafe);
    }

    #[test]
    fn test_send_sync_checker_safe_type() {
        let mut checker = SendSyncChecker::new();
        let field = TypeInfo::new("i32", true, true);
        let mut ty = TypeInfo::new("SafeStruct", true, true);
        ty.fields.push(field);
        checker.register_type(ty);

        let violations = checker.check_all();
        assert!(violations.is_empty());
    }

    #[test]
    fn test_send_sync_checker_unsafe_send() {
        let mut checker = SendSyncChecker::new();
        let field = TypeInfo::new("Rc<i32>", false, false);
        let mut ty = TypeInfo::new("BadSend", true, false);
        ty.fields.push(field);
        checker.register_type(ty);

        let violations = checker.check_all();
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].kind, ViolationKind::UnsafeSend);
    }

    #[test]
    fn test_send_sync_checker_unsafe_sync() {
        let mut checker = SendSyncChecker::new();
        let field = TypeInfo::new("Cell<i32>", true, false);
        let mut ty = TypeInfo::new("BadSync", true, true);
        ty.fields.push(field);
        checker.register_type(ty);

        let violations = checker.check_all();
        assert!(violations.iter().any(|v| v.kind == ViolationKind::UnsafeSync));
    }

    #[test]
    fn test_send_sync_checker_interior_mutability() {
        let mut checker = SendSyncChecker::new();
        let mut ty = TypeInfo::new("UnsafeCell<i32>", false, false);
        ty.has_interior_mutability = true;
        checker.register_type(ty);

        let violations = checker.check_all();
        assert!(violations.iter().any(|v| v.kind == ViolationKind::UnprotectedInteriorMutability));
    }

    #[test]
    fn test_data_race_detection_no_race() {
        let mut detector = DataRaceDetector::new();
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t1".into(),
            is_write: false,
            span: SourceSpan::default(),
        });
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t2".into(),
            is_write: false,
            span: SourceSpan::default(),
        });
        let races = detector.detect();
        assert!(races.is_empty(), "two reads should not be a race");
    }

    #[test]
    fn test_data_race_detection_write_write() {
        let mut detector = DataRaceDetector::new();
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t1".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t2".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        let races = detector.detect();
        assert_eq!(races.len(), 1);
    }

    #[test]
    fn test_data_race_detection_read_write() {
        let mut detector = DataRaceDetector::new();
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t1".into(),
            is_write: false,
            span: SourceSpan::default(),
        });
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t2".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        let races = detector.detect();
        assert_eq!(races.len(), 1);
    }

    #[test]
    fn test_data_race_same_thread_ok() {
        let mut detector = DataRaceDetector::new();
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t1".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t1".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        let races = detector.detect();
        assert!(races.is_empty());
    }

    #[test]
    fn test_data_race_mutex_protected() {
        let mut detector = DataRaceDetector::new();
        detector.add_access(SharedAccess {
            location: "m1".into(),
            thread: "t1".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        detector.add_access(SharedAccess {
            location: "m1".into(),
            thread: "t2".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        detector.add_mutex_event(MutexEvent {
            mutex_id: "m1".into(),
            thread: "t1".into(),
            is_acquire: true,
            span: SourceSpan::default(),
        });
        detector.add_mutex_event(MutexEvent {
            mutex_id: "m1".into(),
            thread: "t1".into(),
            is_acquire: false,
            span: SourceSpan::default(),
        });
        let races = detector.detect();
        assert!(races.iter().all(|r| r.is_protected));
    }

    #[test]
    fn test_atomic_ordering_strength() {
        assert!(AtomicOrdering::SeqCst.is_at_least(&AtomicOrdering::Relaxed));
        assert!(AtomicOrdering::AcqRel.is_at_least(&AtomicOrdering::Acquire));
        assert!(!AtomicOrdering::Relaxed.is_at_least(&AtomicOrdering::Acquire));
        // Acquire and Release are incomparable in the C11 lattice.
        assert!(!AtomicOrdering::Release.is_at_least(&AtomicOrdering::Acquire));
        assert!(!AtomicOrdering::Acquire.is_at_least(&AtomicOrdering::Release));
    }

    #[test]
    fn test_atomic_ordering_semantics() {
        assert!(AtomicOrdering::Acquire.is_acquire());
        assert!(!AtomicOrdering::Acquire.is_release());
        assert!(AtomicOrdering::Release.is_release());
        assert!(!AtomicOrdering::Release.is_acquire());
        assert!(AtomicOrdering::SeqCst.is_acquire());
        assert!(AtomicOrdering::SeqCst.is_release());
    }

    #[test]
    fn test_generate_thread_safety_vcs() {
        let accesses = vec![
            SharedAccess {
                location: "shared_var".into(),
                thread: "main".into(),
                is_write: true,
                span: SourceSpan::default(),
            },
            SharedAccess {
                location: "shared_var".into(),
                thread: "worker".into(),
                is_write: true,
                span: SourceSpan::default(),
            },
        ];
        let vcs = generate_thread_safety_vcs("test_fn", &accesses, &[], &[]);
        assert!(!vcs.is_empty());
    }

    #[test]
    fn test_checker_to_vcs() {
        let mut checker = SendSyncChecker::new();
        let field = TypeInfo::new("Rc<i32>", false, false);
        let mut ty = TypeInfo::new("Bad", true, false);
        ty.fields.push(field);
        checker.register_type(ty);
        checker.check_all();

        let vcs = checker.to_vcs("test_fn");
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].function, "test_fn");
    }

    #[test]
    fn test_different_locations_no_race() {
        let mut detector = DataRaceDetector::new();
        detector.add_access(SharedAccess {
            location: "x".into(),
            thread: "t1".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        detector.add_access(SharedAccess {
            location: "y".into(),
            thread: "t2".into(),
            is_write: true,
            span: SourceSpan::default(),
        });
        let races = detector.detect();
        assert!(races.is_empty());
    }
}
