// trust_vcgen/data_race.rs: Data race detection and memory ordering verification
//
// Implements happens-before analysis for shared memory accesses across threads.
// Detects potential data races (two accesses to the same variable from different
// threads, at least one a write, with no happens-before ordering) and generates
// VCs asserting each race is infeasible. Also checks that atomic operations use
// sufficiently strong memory orderings for correctness.
//
// Part of #203: Data race / atomics / memory ordering verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{
    AtomicOrdering, AtomicRmwOp, Formula, Sort, SourceSpan, VcKind, VerificationCondition,
};

fn generated_data_race_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("data_race", unqualified)
}

/// Memory ordering levels for atomic operations, mirroring `std::sync::atomic::Ordering`.
///
/// Ordered by strength: Relaxed < Acquire/Release < AcqRel < SeqCst.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MemoryOrdering {
    /// No synchronization guarantees beyond atomicity.
    Relaxed,
    /// Acquire: loads see all writes from the releasing thread.
    Acquire,
    /// Release: all prior writes become visible to acquiring threads.
    Release,
    /// Both Acquire and Release semantics.
    AcqRel,
    /// Sequentially consistent: total global ordering of all SeqCst operations.
    SeqCst,
}

impl MemoryOrdering {
    /// Human-readable name for diagnostics.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            MemoryOrdering::Relaxed => "Relaxed",
            MemoryOrdering::Acquire => "Acquire",
            MemoryOrdering::Release => "Release",
            MemoryOrdering::AcqRel => "AcqRel",
            MemoryOrdering::SeqCst => "SeqCst",
        }
    }

    /// Returns true if this ordering is at least as strong as `other`.
    ///
    /// The ordering lattice:
    /// - Relaxed is weaker than everything.
    /// - Acquire and Release are incomparable (neither implies the other).
    /// - AcqRel is stronger than both Acquire and Release.
    /// - SeqCst is stronger than everything.
    #[must_use]
    pub fn is_at_least(&self, other: MemoryOrdering) -> bool {
        match (self, other) {
            // SeqCst satisfies everything.
            (MemoryOrdering::SeqCst, _) => true,
            // AcqRel satisfies Acquire, Release, AcqRel, and Relaxed.
            (MemoryOrdering::AcqRel, MemoryOrdering::SeqCst) => false,
            (MemoryOrdering::AcqRel, _) => true,
            // Acquire satisfies Acquire and Relaxed only.
            (MemoryOrdering::Acquire, MemoryOrdering::Acquire | MemoryOrdering::Relaxed) => true,
            (MemoryOrdering::Acquire, _) => false,
            // Release satisfies Release and Relaxed only.
            (MemoryOrdering::Release, MemoryOrdering::Release | MemoryOrdering::Relaxed) => true,
            (MemoryOrdering::Release, _) => false,
            // Relaxed only satisfies Relaxed.
            (MemoryOrdering::Relaxed, MemoryOrdering::Relaxed) => true,
            (MemoryOrdering::Relaxed, _) => false,
        }
    }
}

// Trust: #612 -- Bridge impls between MemoryOrdering (local, data_race analysis)
// and AtomicOrdering (canonical, trust_types). These allow conversion when
// passing between the MIR extraction layer (AtomicOrdering) and the VC
// generation layer (MemoryOrdering).
impl From<AtomicOrdering> for MemoryOrdering {
    fn from(ao: AtomicOrdering) -> Self {
        match ao {
            AtomicOrdering::Relaxed => MemoryOrdering::Relaxed,
            AtomicOrdering::Acquire => MemoryOrdering::Acquire,
            AtomicOrdering::Release => MemoryOrdering::Release,
            AtomicOrdering::AcqRel => MemoryOrdering::AcqRel,
            AtomicOrdering::SeqCst => MemoryOrdering::SeqCst,
            // Trust: conservative fallback for #[non_exhaustive] -- SeqCst is strongest.
            _ => MemoryOrdering::SeqCst,
        }
    }
}

// Trust: #612 — Reverse bridge from local MemoryOrdering to canonical AtomicOrdering.
impl From<MemoryOrdering> for AtomicOrdering {
    fn from(mo: MemoryOrdering) -> Self {
        match mo {
            MemoryOrdering::Relaxed => AtomicOrdering::Relaxed,
            MemoryOrdering::Acquire => AtomicOrdering::Acquire,
            MemoryOrdering::Release => AtomicOrdering::Release,
            MemoryOrdering::AcqRel => AtomicOrdering::AcqRel,
            MemoryOrdering::SeqCst => AtomicOrdering::SeqCst,
        }
    }
}

/// The kind of memory access.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AccessKind {
    /// Non-atomic read.
    Read,
    /// Non-atomic write.
    Write,
    /// Atomic read with the specified ordering.
    AtomicRead(MemoryOrdering),
    /// Atomic write with the specified ordering.
    AtomicWrite(MemoryOrdering),
    /// Atomic read-modify-write with the specified ordering and sub-operation.
    ///
    /// RMW operations (compare_exchange, fetch_add, swap, etc.) are both a read
    /// and a write atomically. They have combined acquire+release semantics when
    /// AcqRel is used and participate in release sequences. Splitting them into
    /// separate AtomicRead + AtomicWrite would lose the atomicity guarantee.
    /// They DO race with non-atomic accesses to the same location.
    // Trust: #612 -- RMW operations need distinct treatment in HB analysis.
    AtomicRmw(MemoryOrdering, AtomicRmwOp),
    /// Memory fence with the specified ordering.
    Fence(MemoryOrdering),
}

impl AccessKind {
    /// Returns true if this access is a write (atomic or not).
    ///
    /// `AtomicRmw` counts as a write because it modifies the memory location.
    #[must_use]
    pub fn is_write(&self) -> bool {
        matches!(self, AccessKind::Write | AccessKind::AtomicWrite(_) | AccessKind::AtomicRmw(..))
    }

    /// Returns true if this access is a read (atomic or not).
    ///
    /// `AtomicRmw` counts as a read because it reads the memory location.
    #[must_use]
    pub fn is_read(&self) -> bool {
        matches!(self, AccessKind::Read | AccessKind::AtomicRead(_) | AccessKind::AtomicRmw(..))
    }

    /// Returns true if this is a non-atomic access.
    #[must_use]
    pub fn is_non_atomic(&self) -> bool {
        matches!(self, AccessKind::Read | AccessKind::Write)
    }

    /// Returns the memory ordering, if any.
    #[must_use]
    pub fn ordering(&self) -> Option<MemoryOrdering> {
        match self {
            AccessKind::AtomicRead(o)
            | AccessKind::AtomicWrite(o)
            | AccessKind::Fence(o)
            | AccessKind::AtomicRmw(o, _) => Some(*o),
            AccessKind::Read | AccessKind::Write => None,
        }
    }
}

/// A single access to shared memory.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SharedAccess {
    /// Name of the shared variable being accessed.
    pub variable: String,
    /// What kind of access this is.
    pub access_kind: AccessKind,
    /// Identifier for the thread performing the access.
    pub thread_id: String,
    /// Identifiers of accesses that happen-before this one.
    ///
    /// Each entry is the index into the access list. An access at index `i` is
    /// ordered before this access if `i` appears in `happens_before`.
    pub happens_before: Vec<usize>,
    /// Source location of this access (for diagnostics).
    pub span: SourceSpan,
}

/// A pair of accesses that constitute a potential data race.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataRacePair {
    /// Index of the first access in the original access list.
    pub first: usize,
    /// Index of the second access in the original access list.
    pub second: usize,
    /// The shared variable involved.
    pub variable: String,
    /// Thread ID of the first access.
    pub thread_a: String,
    /// Thread ID of the second access.
    pub thread_b: String,
}

/// Detect potential data races in a set of shared memory accesses.
///
/// A data race exists when:
/// 1. Two accesses target the same variable.
/// 2. They originate from different threads.
/// 3. At least one is a write.
/// 4. There is no happens-before relationship between them.
///
/// Fences are not direct accesses; they establish ordering but do not
/// themselves race. We skip them.
#[must_use]
pub fn detect_potential_races(accesses: &[SharedAccess]) -> Vec<DataRacePair> {
    let mut races = Vec::new();

    for (i, a) in accesses.iter().enumerate() {
        // Skip fences -- they are not data accesses.
        if matches!(a.access_kind, AccessKind::Fence(_)) {
            continue;
        }

        for (j, b) in accesses.iter().enumerate().skip(i + 1) {
            if matches!(b.access_kind, AccessKind::Fence(_)) {
                continue;
            }

            // (1) Same variable
            if a.variable != b.variable {
                continue;
            }

            // (2) Different threads
            if a.thread_id == b.thread_id {
                continue;
            }

            // (3) At least one write
            if !a.access_kind.is_write() && !b.access_kind.is_write() {
                continue;
            }

            // (4) No happens-before in either direction
            if has_happens_before(accesses, i, j) || has_happens_before(accesses, j, i) {
                continue;
            }

            // Both non-atomic => definitely a race candidate.
            // One atomic + one non-atomic => still a race (non-atomic access is unordered).
            // Both atomic => not a data race (atomics are defined to not race),
            // but ordering may be insufficient (checked separately).
            if !a.access_kind.is_non_atomic() && !b.access_kind.is_non_atomic() {
                continue;
            }

            races.push(DataRacePair {
                first: i,
                second: j,
                variable: a.variable.clone(),
                thread_a: a.thread_id.clone(),
                thread_b: b.thread_id.clone(),
            });
        }
    }

    races
}

/// Check whether access `from` transitively happens-before access `to`.
///
/// Uses a simple BFS over the happens-before graph.
fn has_happens_before(accesses: &[SharedAccess], from: usize, to: usize) -> bool {
    if accesses[to].happens_before.contains(&from) {
        return true;
    }

    // Transitive closure via BFS
    let mut visited = vec![false; accesses.len()];
    let mut queue = std::collections::VecDeque::new();

    for &dep in &accesses[to].happens_before {
        if dep < accesses.len() {
            queue.push_back(dep);
            visited[dep] = true;
        }
    }

    while let Some(current) = queue.pop_front() {
        if current == from {
            return true;
        }
        for &dep in &accesses[current].happens_before {
            if dep < accesses.len() && !visited[dep] {
                visited[dep] = true;
                queue.push_back(dep);
            }
        }
    }

    false
}

/// Generate verification conditions asserting that each detected data race is
/// infeasible.
///
/// For each race pair, we generate a VC whose formula, if SAT, means the
/// race can occur. The convention is: SAT = violation found, UNSAT = safe.
///
/// The formula encodes: both threads can reach their access points simultaneously
/// (both reach conditions are satisfiable) AND no synchronization establishes
/// ordering. This is represented as `reach_a AND reach_b AND NOT(ordered)`.
#[must_use]
pub fn generate_race_vcs(
    races: &[DataRacePair],
    function_name: &str,
    accesses: &[SharedAccess],
) -> Vec<VerificationCondition> {
    races
        .iter()
        .map(|race| {
            let span = accesses.get(race.first).map(|a| a.span.clone()).unwrap_or_default();

            // Symbolic variables representing reachability of each access point.
            let reach_a = Formula::Var(
                generated_data_race_symbol(&format!("reach_{}_{}", race.thread_a, race.first)),
                Sort::Bool,
            );
            let reach_b = Formula::Var(
                generated_data_race_symbol(&format!("reach_{}_{}", race.thread_b, race.second)),
                Sort::Bool,
            );

            // The "ordered" variable represents whether synchronization
            // establishes a happens-before edge. If we already determined
            // there is no HB edge (that's why it's in the race list), this
            // is simply `false` -- meaning NOT(ordered) is true.
            let not_ordered = Formula::Bool(true);

            // VC formula: both accesses reachable AND not ordered.
            let formula = Formula::And(vec![reach_a, reach_b, not_ordered]);

            VerificationCondition {
                kind: VcKind::DataRace {
                    variable: race.variable.clone(),
                    thread_a: race.thread_a.clone(),
                    thread_b: race.thread_b.clone(),
                },
                function: function_name.into(),
                location: span,
                formula,
                contract_metadata: None,
            }
        })
        .collect()
}

/// Check whether a given access's memory ordering is at least as strong as
/// `required`.
///
/// Returns `true` if the ordering is sufficient, `false` if it is too weak.
/// Non-atomic accesses always return `false` (they have no ordering at all).
#[must_use]
pub fn check_ordering_sufficient(access: &SharedAccess, required: MemoryOrdering) -> bool {
    match access.access_kind.ordering() {
        Some(actual) => actual.is_at_least(required),
        // Non-atomic accesses have no ordering.
        None => false,
    }
}

/// Generate VCs for insufficient memory orderings on atomic accesses.
///
/// For each atomic access paired with a required ordering, if the access
/// uses a weaker ordering, generate a VC. The VC asserts the access is
/// reachable with insufficient ordering.
#[must_use]
pub fn generate_ordering_vcs(
    accesses: &[SharedAccess],
    requirements: &[(usize, MemoryOrdering)],
    function_name: &str,
) -> Vec<VerificationCondition> {
    requirements
        .iter()
        .filter_map(|&(idx, required)| {
            let access = accesses.get(idx)?;
            let actual_ordering = access.access_kind.ordering()?;

            if actual_ordering.is_at_least(required) {
                return None;
            }

            let reach = Formula::Var(
                generated_data_race_symbol(&format!("reach_{}_{}", access.thread_id, idx)),
                Sort::Bool,
            );

            Some(VerificationCondition {
                kind: VcKind::InsufficientOrdering {
                    variable: access.variable.clone(),
                    actual: actual_ordering.name().to_string(),
                    required: required.name().to_string(),
                },
                function: function_name.into(),
                location: access.span.clone(),
                formula: reach,
                contract_metadata: None,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_access(variable: &str, kind: AccessKind, thread: &str, hb: Vec<usize>) -> SharedAccess {
        SharedAccess {
            variable: variable.to_string(),
            access_kind: kind,
            thread_id: thread.to_string(),
            happens_before: hb,
            span: SourceSpan::default(),
        }
    }

    // -----------------------------------------------------------------------
    // MemoryOrdering tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_ordering_names() {
        assert_eq!(MemoryOrdering::Relaxed.name(), "Relaxed");
        assert_eq!(MemoryOrdering::Acquire.name(), "Acquire");
        assert_eq!(MemoryOrdering::Release.name(), "Release");
        assert_eq!(MemoryOrdering::AcqRel.name(), "AcqRel");
        assert_eq!(MemoryOrdering::SeqCst.name(), "SeqCst");
    }

    #[test]
    fn test_ordering_is_at_least_seqcst_satisfies_all() {
        assert!(MemoryOrdering::SeqCst.is_at_least(MemoryOrdering::Relaxed));
        assert!(MemoryOrdering::SeqCst.is_at_least(MemoryOrdering::Acquire));
        assert!(MemoryOrdering::SeqCst.is_at_least(MemoryOrdering::Release));
        assert!(MemoryOrdering::SeqCst.is_at_least(MemoryOrdering::AcqRel));
        assert!(MemoryOrdering::SeqCst.is_at_least(MemoryOrdering::SeqCst));
    }

    #[test]
    fn test_ordering_acqrel_satisfies_acquire_release() {
        assert!(MemoryOrdering::AcqRel.is_at_least(MemoryOrdering::Relaxed));
        assert!(MemoryOrdering::AcqRel.is_at_least(MemoryOrdering::Acquire));
        assert!(MemoryOrdering::AcqRel.is_at_least(MemoryOrdering::Release));
        assert!(MemoryOrdering::AcqRel.is_at_least(MemoryOrdering::AcqRel));
        assert!(!MemoryOrdering::AcqRel.is_at_least(MemoryOrdering::SeqCst));
    }

    #[test]
    fn test_ordering_acquire_release_incomparable() {
        assert!(!MemoryOrdering::Acquire.is_at_least(MemoryOrdering::Release));
        assert!(!MemoryOrdering::Release.is_at_least(MemoryOrdering::Acquire));
    }

    #[test]
    fn test_ordering_relaxed_only_satisfies_relaxed() {
        assert!(MemoryOrdering::Relaxed.is_at_least(MemoryOrdering::Relaxed));
        assert!(!MemoryOrdering::Relaxed.is_at_least(MemoryOrdering::Acquire));
        assert!(!MemoryOrdering::Relaxed.is_at_least(MemoryOrdering::Release));
        assert!(!MemoryOrdering::Relaxed.is_at_least(MemoryOrdering::AcqRel));
        assert!(!MemoryOrdering::Relaxed.is_at_least(MemoryOrdering::SeqCst));
    }

    // -----------------------------------------------------------------------
    // AccessKind tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_access_kind_is_write() {
        assert!(!AccessKind::Read.is_write());
        assert!(AccessKind::Write.is_write());
        assert!(!AccessKind::AtomicRead(MemoryOrdering::Acquire).is_write());
        assert!(AccessKind::AtomicWrite(MemoryOrdering::Release).is_write());
        assert!(AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add).is_write());
        assert!(!AccessKind::Fence(MemoryOrdering::SeqCst).is_write());
    }

    #[test]
    fn test_access_kind_is_read() {
        assert!(AccessKind::Read.is_read());
        assert!(!AccessKind::Write.is_read());
        assert!(AccessKind::AtomicRead(MemoryOrdering::Acquire).is_read());
        assert!(!AccessKind::AtomicWrite(MemoryOrdering::Release).is_read());
        assert!(AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add).is_read());
        assert!(!AccessKind::Fence(MemoryOrdering::SeqCst).is_read());
    }

    #[test]
    fn test_access_kind_is_non_atomic() {
        assert!(AccessKind::Read.is_non_atomic());
        assert!(AccessKind::Write.is_non_atomic());
        assert!(!AccessKind::AtomicRead(MemoryOrdering::Relaxed).is_non_atomic());
        assert!(!AccessKind::AtomicWrite(MemoryOrdering::Relaxed).is_non_atomic());
        assert!(!AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add).is_non_atomic());
        assert!(!AccessKind::Fence(MemoryOrdering::SeqCst).is_non_atomic());
    }

    #[test]
    fn test_access_kind_ordering() {
        assert_eq!(AccessKind::Read.ordering(), None);
        assert_eq!(AccessKind::Write.ordering(), None);
        assert_eq!(
            AccessKind::AtomicRead(MemoryOrdering::Acquire).ordering(),
            Some(MemoryOrdering::Acquire)
        );
        assert_eq!(
            AccessKind::AtomicWrite(MemoryOrdering::Release).ordering(),
            Some(MemoryOrdering::Release)
        );
        assert_eq!(
            AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add).ordering(),
            Some(MemoryOrdering::AcqRel)
        );
        assert_eq!(
            AccessKind::Fence(MemoryOrdering::SeqCst).ordering(),
            Some(MemoryOrdering::SeqCst)
        );
    }

    // -----------------------------------------------------------------------
    // From bridge tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_from_atomic_ordering_to_memory_ordering() {
        assert_eq!(MemoryOrdering::from(AtomicOrdering::Relaxed), MemoryOrdering::Relaxed);
        assert_eq!(MemoryOrdering::from(AtomicOrdering::Acquire), MemoryOrdering::Acquire);
        assert_eq!(MemoryOrdering::from(AtomicOrdering::Release), MemoryOrdering::Release);
        assert_eq!(MemoryOrdering::from(AtomicOrdering::AcqRel), MemoryOrdering::AcqRel);
        assert_eq!(MemoryOrdering::from(AtomicOrdering::SeqCst), MemoryOrdering::SeqCst);
    }

    #[test]
    fn test_from_memory_ordering_to_atomic_ordering() {
        assert_eq!(AtomicOrdering::from(MemoryOrdering::Relaxed), AtomicOrdering::Relaxed);
        assert_eq!(AtomicOrdering::from(MemoryOrdering::Acquire), AtomicOrdering::Acquire);
        assert_eq!(AtomicOrdering::from(MemoryOrdering::Release), AtomicOrdering::Release);
        assert_eq!(AtomicOrdering::from(MemoryOrdering::AcqRel), AtomicOrdering::AcqRel);
        assert_eq!(AtomicOrdering::from(MemoryOrdering::SeqCst), AtomicOrdering::SeqCst);
    }

    #[test]
    fn test_from_roundtrip() {
        for mo in [
            MemoryOrdering::Relaxed,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            MemoryOrdering::AcqRel,
            MemoryOrdering::SeqCst,
        ] {
            let ao: AtomicOrdering = mo.into();
            let back: MemoryOrdering = ao.into();
            assert_eq!(back, mo, "roundtrip failed for {mo:?}");
        }
    }

    // -----------------------------------------------------------------------
    // AtomicRmw tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_atomic_rmw_is_both_read_and_write() {
        let rmw = AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add);
        assert!(rmw.is_read(), "RMW should be a read");
        assert!(rmw.is_write(), "RMW should be a write");
        assert!(!rmw.is_non_atomic(), "RMW should be atomic");
    }

    #[test]
    fn test_no_race_both_atomic_rmw() {
        // Two AtomicRmw accesses from different threads should not race.
        let accesses = vec![
            make_access(
                "counter",
                AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add),
                "t1",
                vec![],
            ),
            make_access(
                "counter",
                AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add),
                "t2",
                vec![],
            ),
        ];
        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "two atomic RMW accesses should not race");
    }

    #[test]
    fn test_race_rmw_vs_non_atomic() {
        // AtomicRmw + non-atomic read => race.
        let accesses = vec![
            make_access(
                "x",
                AccessKind::AtomicRmw(MemoryOrdering::Relaxed, AtomicRmwOp::Add),
                "t1",
                vec![],
            ),
            make_access("x", AccessKind::Read, "t2", vec![]),
        ];
        let races = detect_potential_races(&accesses);
        assert_eq!(races.len(), 1, "RMW + non-atomic access should race");
    }

    // -----------------------------------------------------------------------
    // Race detection tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_detect_race_two_threads_write_read_no_sync() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("x", AccessKind::Read, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert_eq!(races.len(), 1);
        assert_eq!(races[0].variable, "x");
        assert_eq!(races[0].thread_a, "t1");
        assert_eq!(races[0].thread_b, "t2");
    }

    #[test]
    fn test_no_race_same_thread() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("x", AccessKind::Read, "t1", vec![0]),
        ];

        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "same-thread accesses cannot race");
    }

    #[test]
    fn test_no_race_two_reads() {
        let accesses = vec![
            make_access("x", AccessKind::Read, "t1", vec![]),
            make_access("x", AccessKind::Read, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "two reads cannot race");
    }

    #[test]
    fn test_no_race_different_variables() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("y", AccessKind::Write, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "different variables cannot race");
    }

    #[test]
    fn test_no_race_with_happens_before() {
        // t1 writes x, then t2 reads x with happens-before on t1's write.
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("x", AccessKind::Read, "t2", vec![0]),
        ];

        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "happens-before ordering prevents race");
    }

    #[test]
    fn test_no_race_with_transitive_happens_before() {
        // t1 writes x (0), t1 signals (1, hb on 0), t2 waits (2, hb on 1), t2 reads x (3, hb on 2).
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("signal", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1", vec![0]),
            make_access("signal", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2", vec![1]),
            make_access("x", AccessKind::Read, "t2", vec![2]),
        ];

        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "transitive HB should prevent race on x");
    }

    #[test]
    fn test_race_write_write_no_sync() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("x", AccessKind::Write, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert_eq!(races.len(), 1, "write-write race should be detected");
    }

    #[test]
    fn test_no_race_both_atomic() {
        // Two atomic accesses to the same variable from different threads:
        // atomics do not constitute a data race (they are well-defined).
        let accesses = vec![
            make_access("x", AccessKind::AtomicWrite(MemoryOrdering::Relaxed), "t1", vec![]),
            make_access("x", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert!(races.is_empty(), "two atomic accesses do not race");
    }

    #[test]
    fn test_race_atomic_vs_non_atomic() {
        // One atomic write + one non-atomic read => still a data race.
        let accesses = vec![
            make_access("x", AccessKind::AtomicWrite(MemoryOrdering::Relaxed), "t1", vec![]),
            make_access("x", AccessKind::Read, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert_eq!(races.len(), 1, "atomic + non-atomic access to same var is a race");
    }

    #[test]
    fn test_fences_are_skipped() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("fence", AccessKind::Fence(MemoryOrdering::SeqCst), "t1", vec![0]),
            make_access("x", AccessKind::Read, "t2", vec![]),
        ];

        // The fence itself should not participate in race pairs.
        let races = detect_potential_races(&accesses);
        assert_eq!(races.len(), 1, "fence does not prevent race (no HB established to t2)");
        assert_eq!(races[0].first, 0);
        assert_eq!(races[0].second, 2);
    }

    #[test]
    fn test_multiple_races_detected() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("x", AccessKind::Read, "t2", vec![]),
            make_access("y", AccessKind::Write, "t1", vec![]),
            make_access("y", AccessKind::Write, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        assert_eq!(races.len(), 2, "should find race on x and race on y");
    }

    #[test]
    fn test_empty_accesses() {
        let races = detect_potential_races(&[]);
        assert!(races.is_empty());
    }

    #[test]
    fn test_single_access() {
        let accesses = vec![make_access("x", AccessKind::Write, "t1", vec![])];
        let races = detect_potential_races(&accesses);
        assert!(races.is_empty());
    }

    // -----------------------------------------------------------------------
    // VC generation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_race_vcs_produces_correct_kinds() {
        let accesses = vec![
            make_access("counter", AccessKind::Write, "t1", vec![]),
            make_access("counter", AccessKind::Read, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        let vcs = generate_race_vcs(&races, "increment", &accesses);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::DataRace { variable, thread_a, thread_b }
                if variable == "counter" && thread_a == "t1" && thread_b == "t2"
        ));
        assert_eq!(vcs[0].function, "increment");
        assert_eq!(vcs[0].kind.proof_level(), trust_types::ProofLevel::L0Safety);
    }

    #[test]
    fn test_generate_race_vcs_formula_structure() {
        let accesses = vec![
            make_access("x", AccessKind::Write, "t1", vec![]),
            make_access("x", AccessKind::Write, "t2", vec![]),
        ];

        let races = detect_potential_races(&accesses);
        let vcs = generate_race_vcs(&races, "test_fn", &accesses);

        assert_eq!(vcs.len(), 1);
        // Generated reachability symbols must stay outside the source namespace.
        let expected_a = generated_data_race_symbol("reach_t1_0");
        let expected_b = generated_data_race_symbol("reach_t2_1");
        match &vcs[0].formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 3);
                assert!(matches!(
                    &clauses[0],
                    Formula::Var(name, Sort::Bool) if name == &expected_a
                ));
                assert!(matches!(
                    &clauses[1],
                    Formula::Var(name, Sort::Bool) if name == &expected_b
                ));
                assert_ne!(expected_a, "reach_t1_0");
                assert_ne!(expected_b, "reach_t2_1");
                assert!(matches!(&clauses[2], Formula::Bool(true)));
            }
            other => panic!("expected And formula, got: {other:?}"),
        }
    }

    #[test]
    fn test_generate_race_vcs_empty_races() {
        let vcs = generate_race_vcs(&[], "test_fn", &[]);
        assert!(vcs.is_empty());
    }

    // -----------------------------------------------------------------------
    // Ordering sufficiency tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_ordering_sufficient_seqcst_always_enough() {
        let access = make_access("x", AccessKind::AtomicRead(MemoryOrdering::SeqCst), "t1", vec![]);
        assert!(check_ordering_sufficient(&access, MemoryOrdering::Relaxed));
        assert!(check_ordering_sufficient(&access, MemoryOrdering::Acquire));
        assert!(check_ordering_sufficient(&access, MemoryOrdering::Release));
        assert!(check_ordering_sufficient(&access, MemoryOrdering::AcqRel));
        assert!(check_ordering_sufficient(&access, MemoryOrdering::SeqCst));
    }

    #[test]
    fn test_check_ordering_insufficient_relaxed_for_acquire() {
        let access =
            make_access("x", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t1", vec![]);
        assert!(!check_ordering_sufficient(&access, MemoryOrdering::Acquire));
    }

    #[test]
    fn test_check_ordering_non_atomic_always_insufficient() {
        let access = make_access("x", AccessKind::Read, "t1", vec![]);
        assert!(!check_ordering_sufficient(&access, MemoryOrdering::Relaxed));
    }

    #[test]
    fn test_check_ordering_acquire_satisfies_acquire() {
        let access =
            make_access("x", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t1", vec![]);
        assert!(check_ordering_sufficient(&access, MemoryOrdering::Acquire));
    }

    #[test]
    fn test_check_ordering_release_does_not_satisfy_acquire() {
        let access =
            make_access("x", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1", vec![]);
        assert!(!check_ordering_sufficient(&access, MemoryOrdering::Acquire));
    }

    // -----------------------------------------------------------------------
    // Ordering VC generation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_ordering_vcs_insufficient() {
        let accesses = vec![make_access(
            "flag",
            AccessKind::AtomicRead(MemoryOrdering::Relaxed),
            "t1",
            vec![],
        )];
        let requirements = vec![(0, MemoryOrdering::Acquire)];

        let vcs = generate_ordering_vcs(&accesses, &requirements, "spin_wait");
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::InsufficientOrdering { variable, actual, required }
                if variable == "flag" && actual == "Relaxed" && required == "Acquire"
        ));
        assert_eq!(
            vcs[0].formula,
            Formula::Var(generated_data_race_symbol("reach_t1_0"), Sort::Bool)
        );
        assert_ne!(vcs[0].formula.var_name(), Some("reach_t1_0"));
    }

    #[test]
    fn test_generate_ordering_vcs_sufficient_no_vc() {
        let accesses =
            vec![make_access("flag", AccessKind::AtomicRead(MemoryOrdering::SeqCst), "t1", vec![])];
        let requirements = vec![(0, MemoryOrdering::Acquire)];

        let vcs = generate_ordering_vcs(&accesses, &requirements, "spin_wait");
        assert!(vcs.is_empty(), "sufficient ordering should not produce a VC");
    }

    #[test]
    fn test_generate_ordering_vcs_non_atomic_skipped() {
        let accesses = vec![make_access("x", AccessKind::Read, "t1", vec![])];
        // Non-atomic accesses have no ordering, so ordering() returns None
        // and we skip (filter_map returns None).
        let requirements = vec![(0, MemoryOrdering::Acquire)];
        let vcs = generate_ordering_vcs(&accesses, &requirements, "test_fn");
        assert!(vcs.is_empty(), "non-atomic access has no ordering to check");
    }

    #[test]
    fn test_generate_ordering_vcs_mixed() {
        let accesses = vec![
            make_access("a", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t1", vec![]),
            make_access("b", AccessKind::AtomicWrite(MemoryOrdering::SeqCst), "t1", vec![]),
            make_access("c", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2", vec![]),
        ];
        let requirements = vec![
            (0, MemoryOrdering::Acquire), // Relaxed < Acquire => VC
            (1, MemoryOrdering::Release), // SeqCst >= Release => no VC
            (2, MemoryOrdering::SeqCst),  // Acquire < SeqCst => VC
        ];

        let vcs = generate_ordering_vcs(&accesses, &requirements, "test_fn");
        assert_eq!(vcs.len(), 2, "should generate VCs for the two insufficient orderings");
    }

    // -----------------------------------------------------------------------
    // Serialization roundtrip tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_memory_ordering_serialization_roundtrip() {
        let orderings = vec![
            MemoryOrdering::Relaxed,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            MemoryOrdering::AcqRel,
            MemoryOrdering::SeqCst,
        ];
        let json = serde_json::to_string(&orderings).expect("serialize");
        let round: Vec<MemoryOrdering> = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, orderings);
    }

    #[test]
    fn test_access_kind_serialization_roundtrip() {
        let kinds = vec![
            AccessKind::Read,
            AccessKind::Write,
            AccessKind::AtomicRead(MemoryOrdering::Acquire),
            AccessKind::AtomicWrite(MemoryOrdering::Release),
            AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add),
            AccessKind::Fence(MemoryOrdering::SeqCst),
        ];
        let json = serde_json::to_string(&kinds).expect("serialize");
        let round: Vec<AccessKind> = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, kinds);
    }

    #[test]
    fn test_shared_access_serialization_roundtrip() {
        let access = make_access(
            "counter",
            AccessKind::AtomicWrite(MemoryOrdering::Release),
            "t1",
            vec![0, 1],
        );
        let json = serde_json::to_string(&access).expect("serialize");
        let round: SharedAccess = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.variable, "counter");
        assert_eq!(round.access_kind, AccessKind::AtomicWrite(MemoryOrdering::Release));
        assert_eq!(round.happens_before, vec![0, 1]);
    }

    #[test]
    fn test_data_race_pair_serialization_roundtrip() {
        let pair = DataRacePair {
            first: 0,
            second: 3,
            variable: "shared_buf".to_string(),
            thread_a: "producer".to_string(),
            thread_b: "consumer".to_string(),
        };
        let json = serde_json::to_string(&pair).expect("serialize");
        let round: DataRacePair = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, pair);
    }
}
