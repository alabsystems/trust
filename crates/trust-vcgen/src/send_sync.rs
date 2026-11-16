// trust_vcgen/send_sync.rs: Send/Sync concurrency verification
//
// Checks Send/Sync type claims and emits conservative concurrency diagnostics.
// Access and mutex labels do not establish runtime identity or race freedom.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: #612 -- re-export AtomicOrdering from trust_types (canonical, lattice-correct).
// The previous local AtomicOrdering had a buggy derived Ord (Acquire < Release).
// The canonical type correctly models Acquire/Release as incomparable in the C11 lattice.
pub use trust_types::AtomicOrdering;
use trust_types::fx::FxHashMap;
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
    /// Diagnostic location label; different labels do not prove disjointness.
    pub location: String,
    /// Diagnostic thread label, not authenticated runtime identity.
    pub thread: String,
    /// Whether this is a write access.
    pub is_write: bool,
    /// Source location of the access.
    pub span: SourceSpan,
}

/// Caller-supplied mutex-event claim, not authenticated happens-before evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutexEvent {
    /// Diagnostic mutex label, not authenticated lock identity.
    pub mutex_id: String,
    /// Diagnostic thread label, not authenticated runtime identity.
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
        for (name, info) in &self.types {
            Self::check_type_info(name, info, &mut self.violations);
        }
        self.violations.clone()
    }

    /// Check a single type.
    fn check_type_info(name: &str, info: &TypeInfo, violations: &mut Vec<SendSyncViolation>) {
        // If type claims Send, all fields must be Send.
        if info.is_send {
            for field in &info.fields {
                if !field.is_send {
                    violations.push(SendSyncViolation {
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
                    violations.push(SendSyncViolation {
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
            violations.push(SendSyncViolation {
                type_name: name.to_string(),
                kind: ViolationKind::UnprotectedInteriorMutability,
                span: SourceSpan::default(),
                message: format!("type '{}' has interior mutability but is !Sync", name),
            });
        }
    }

    /// Generate VCs from violations.
    pub fn to_vcs(&self, function: &str) -> Vec<VerificationCondition> {
        if self.violations.is_empty() {
            return Vec::new();
        }
        let fn_sym: trust_types::Symbol = function.into();
        self.violations
            .iter()
            .map(|v| {
                VerificationCondition {
                    kind: VcKind::Assertion { message: v.message.clone() },
                    function: fn_sym.clone(),
                    location: v.span.clone(),
                    // POLARITY. This pipeline consumes VIOLATION formulas: SAT
                    // means a counterexample exists, UNSAT means "no violation
                    // reachable" and the row is PROVED (lib.rs:145,
                    // trust-router/src/in_process_ay_backend.rs:24-29). These
                    // rows are minted only for violations the Rust analysis
                    // ALREADY FOUND, so `Bool(false)` asserted the exact
                    // opposite of the finding and the constant folder graded
                    // every detected violation `Proved`.
                    //
                    // `Bool(true)` makes a found violation an undischargeable
                    // obligation, matching `memory_provenance.rs:411`
                    // ("definite violation") and `ffi_vcgen.rs:27-46`.
                    //
                    // This is still a constant, not a proof model. Potential
                    // race candidates are separate UnsupportedMir/Unknown rows;
                    // never reuse this definite-violation polarity for them.
                    formula: Formula::Bool(true),
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
    /// Mutex-event claims retained for diagnostics, never race suppression.
    mutex_events: Vec<MutexEvent>,
}

/// A potential race candidate between two accesses.
#[derive(Debug, Clone)]
pub struct DataRace {
    /// First access.
    pub access1: SharedAccess,
    /// Second access (conflicting).
    pub access2: SharedAccess,
    /// Whether authenticated protection was established; currently always false.
    pub is_protected: bool,
}

impl DataRaceDetector {
    /// Create a new detector.
    pub fn new() -> Self {
        Self { accesses: Vec::new(), mutex_events: Vec::new() }
    }

    /// Record a shared memory access.
    pub fn add_access(&mut self, access: SharedAccess) {
        self.accesses.push(access);
    }

    /// Retain a mutex-event claim for diagnostics only.
    ///
    /// Caller labels and event order cannot establish a held-lock interval.
    pub fn add_mutex_event(&mut self, event: MutexEvent) {
        self.mutex_events.push(event);
    }

    /// Return the caller-supplied mutex-event claims.
    #[must_use]
    pub fn mutex_events(&self) -> &[MutexEvent] {
        &self.mutex_events
    }

    /// Detect all potential data races.
    ///
    /// Any two accesses may alias and come from distinct runtime threads;
    /// diagnostic labels and mutex-event claims cannot discard a conflict.
    pub fn detect(&mut self) -> Vec<DataRace> {
        if self.accesses.len() < 2 || !self.accesses.iter().any(|a| a.is_write) {
            return Vec::new();
        }
        self.candidates()
            .map(|(_, _, a1, a2)| DataRace {
                access1: a1.clone(),
                access2: a2.clone(),
                is_protected: false,
            })
            .collect()
    }

    fn candidates(&self) -> impl Iterator<Item = (usize, usize, &SharedAccess, &SharedAccess)> {
        race_candidates(&self.accesses)
    }

    /// Generate a fail-closed diagnostic VC for every potential race.
    pub fn to_vcs(&self, function: &str) -> Vec<VerificationCondition> {
        race_candidate_vcs(&self.accesses, function)
    }
}

fn race_candidates(
    accesses: &[SharedAccess],
) -> impl Iterator<Item = (usize, usize, &SharedAccess, &SharedAccess)> {
    accesses.iter().enumerate().flat_map(move |(i, a1)| {
        accesses
            .iter()
            .enumerate()
            .skip(i + 1)
            .filter_map(move |(j, a2)| (a1.is_write || a2.is_write).then_some((i, j, a1, a2)))
    })
}

fn race_candidate_vcs(accesses: &[SharedAccess], function: &str) -> Vec<VerificationCondition> {
    if accesses.len() < 2 || !accesses.iter().any(|a| a.is_write) {
        return Vec::new();
    }
    let fn_name: trust_types::Symbol = function.into();
    race_candidates(accesses)
        .map(|(i, j, a1, a2)| {
            let detail = format!(
                "potential conflicting accesses at indices {i} and {j} with spans {:?} and {:?}, \
                 location labels {:?} and {:?}, \
                 thread labels {:?} and {:?}; alias, runtime-thread, and lock-event \
                 identities are unauthenticated",
                a1.span,
                a2.span,
                a1.location,
                a2.location,
                a1.thread,
                a2.thread
            );
            VerificationCondition {
                kind: VcKind::UnsupportedMir { kind: "DataRaceCandidate".to_string(), detail },
                function: fn_name,
                location: a1.span.clone(),
                // The router's UnsupportedMir guard returns Unknown before
                // formula dispatch. True also cannot be accidentally proved
                // by a constant folder if that guard is bypassed.
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            }
        })
        .collect()
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
    _mutex_events: &[MutexEvent],
    atomics: &[AtomicOp],
) -> Vec<VerificationCondition> {
    // Data race VCs.
    let mut vcs = race_candidate_vcs(accesses, function);

    // Atomic ordering VCs.
    vcs.extend(check_atomic_ordering(function, atomics));

    vcs
}

/// Check atomic operations have correct ordering.
fn check_atomic_ordering(function: &str, atomics: &[AtomicOp]) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let mut fn_sym: Option<trust_types::Symbol> = None;

    for op in atomics {
        // Stores need at least Release ordering for publish semantics.
        //
        // `Relaxed` used to be EXCLUDED here by an extra
        // `&& op.ordering != AtomicOrdering::Relaxed` conjunct. With
        // `is_release()` = {Release, AcqRel, SeqCst}, `!is_release()` is
        // {Relaxed, Acquire}, so excluding Relaxed left the arm firing ONLY for
        // an Acquire-ordered store — while the weakest ordering, the one this
        // message exists to report, produced no VC at all. The check reported
        // the odd case and dropped the dangerous one.
        if op.is_store && !op.ordering.is_release() {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "atomic store to '{}' uses {} ordering; Release or stronger recommended",
                        op.variable, op.ordering
                    ),
                },
                function: fn_sym.get_or_insert_with(|| function.into()).clone(),
                location: op.span.clone(),
                // Violation polarity — see `SendSyncChecker::to_vcs`.
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            });
        }

        // Loads need at least Acquire ordering for consume semantics.
        // Same `Relaxed` exclusion as the store arm above, same consequence:
        // `!is_acquire()` is {Relaxed, Release}, so the arm fired only for a
        // Release-ordered load and never for a Relaxed one.
        if !op.is_store && !op.ordering.is_acquire() {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "atomic load from '{}' uses {} ordering; Acquire or stronger recommended",
                        op.variable, op.ordering
                    ),
                },
                function: fn_sym.get_or_insert_with(|| function.into()).clone(),
                location: op.span.clone(),
                // Violation polarity — see `SendSyncChecker::to_vcs`.
                formula: Formula::Bool(true),
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
    fn test_race_vcs_follow_current_accesses_without_detect() {
        let mut detector = DataRaceDetector::new();
        let span = |file: &str| SourceSpan { file: file.into(), ..SourceSpan::default() };
        detector.add_access(SharedAccess {
            location: "same-label".into(),
            thread: "same-thread".into(),
            is_write: false,
            span: span("first.rs"),
        });
        detector.add_access(SharedAccess {
            location: "same-label".into(),
            thread: "same-thread".into(),
            is_write: false,
            span: span("second.rs"),
        });
        assert!(detector.to_vcs("f").is_empty(), "two reads have no race candidate");

        detector.add_access(SharedAccess {
            location: "same-label".into(),
            thread: "same-thread".into(),
            is_write: true,
            span: span("third.rs"),
        });
        let vcs = detector.to_vcs("f");
        assert_eq!(vcs.len(), 2, "VC generation must not require a prior detect call");
        let details: Vec<_> = vcs
            .iter()
            .map(|vc| match &vc.kind {
                VcKind::UnsupportedMir { kind, detail } if kind == "DataRaceCandidate" => {
                    assert!(matches!(&vc.formula, Formula::Bool(true)));
                    detail.as_str()
                }
                other => panic!("expected a fail-closed race candidate, got {other:?}"),
            })
            .collect();
        assert!(details[0].contains("indices 0 and 2"));
        assert!(details[1].contains("indices 1 and 2"));
        assert!(details[0].contains("first.rs") && details[0].contains("third.rs"));
        assert!(details[1].contains("second.rs") && details[1].contains("third.rs"));
        assert_eq!(vcs[0].location, span("first.rs"));
        assert_eq!(vcs[1].location, span("second.rs"));

        assert_eq!(detector.detect().len(), 2);
        detector.add_access(SharedAccess {
            location: "same-label".into(),
            thread: "same-thread".into(),
            is_write: true,
            span: span("fourth.rs"),
        });
        let vcs = detector.to_vcs("f");
        assert_eq!(vcs.len(), 5, "new accesses must not leave the VC population stale");
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "DataRaceCandidate"
                    && detail.contains("indices 2 and 3")
                    && detail.contains("third.rs")
                    && detail.contains("fourth.rs")
        )));
    }

    #[test]
    fn test_same_thread_label_cannot_hide_potential_race() {
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
        assert_eq!(races.len(), 1, "distinct runtime threads can share a label");
        assert_eq!(detector.to_vcs("f").len(), 1);
    }

    #[test]
    fn test_mutex_labels_cannot_protect_a_race() {
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
        assert_eq!(detector.mutex_events().len(), 2);
        assert_eq!(races.len(), 1);
        assert!(!races[0].is_protected, "the claimed lock interval has no event identity");
        assert_eq!(detector.to_vcs("f").len(), 1);
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
    fn test_forged_location_thread_and_mutex_labels_retain_race_vc() {
        let accesses = vec![
            SharedAccess {
                location: "left".into(),
                thread: "worker".into(),
                is_write: true,
                span: SourceSpan::default(),
            },
            SharedAccess {
                location: "right".into(),
                thread: "worker".into(),
                is_write: false,
                span: SourceSpan::default(),
            },
        ];
        let mutex_events = vec![
            MutexEvent {
                mutex_id: "left".into(),
                thread: "worker".into(),
                is_acquire: true,
                span: SourceSpan::default(),
            },
            MutexEvent {
                mutex_id: "left".into(),
                thread: "worker".into(),
                is_acquire: false,
                span: SourceSpan::default(),
            },
        ];

        let vcs = generate_thread_safety_vcs("f", &accesses, &mutex_events, &[]);
        assert_eq!(vcs.len(), 1, "diagnostic names and lock claims cannot erase the pair");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "DataRaceCandidate"
                    && detail.contains("left")
                    && detail.contains("right")
                    && detail.contains("unauthenticated")
        ));
        assert!(matches!(&vcs[0].formula, Formula::Bool(true)));
        assert_eq!(vcs[0].function, "f");
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
    fn test_different_location_labels_may_alias() {
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
        assert_eq!(races.len(), 1, "different diagnostic labels may name the same location");
        assert_eq!(detector.to_vcs("f").len(), 1);
    }
}
