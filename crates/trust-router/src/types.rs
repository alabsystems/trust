//! Core types for the trust-router crate.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

/// Trust: Broad backend role buckets used by routing heuristics.
///
/// These roles let the router prefer a solver family appropriate to a VC
/// before falling back to a general-purpose backend. Future backends can
/// slot into the same ordering without changing call sites.
///
/// # Examples
///
/// ```
/// use trust_router::BackendRole;
///
/// // Each backend advertises its role
/// let role = BackendRole::SmtSolver;
/// assert_ne!(role, BackendRole::General);
///
/// // The router uses roles to rank backends per proof level:
/// // L0Safety prefers AbstractInterpretation > SmtSolver > BoundedModelChecker > ...
/// // L1Functional prefers Deductive > HigherOrder > SmtSolver > ...
/// // L2Domain prefers Temporal > HigherOrder > Deductive > ...
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BackendRole {
    /// Trust: General-purpose or fallback backend.
    General,
    /// Trust: SMT solver backend.
    SmtSolver,
    /// Trust: Bounded model checking backend.
    BoundedModelChecker,
    /// Trust: Deductive verification backend.
    Deductive,
    /// Trust: Ownership/lifetime backend.
    Ownership,
    /// Trust: Temporal verification backend.
    Temporal,
    /// Trust: Higher-order theorem proving backend (e.g., clean).
    HigherOrder,
    /// Trust: In-process abstract-interpretation backend (interval/range
    /// analysis). A cheap front-line for L0 safety obligations, tried before
    /// the SMT solver.
    AbstractInterpretation,
}

/// Trust: Metadata describing one backend in a routed verification plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackendSelection {
    pub index: usize,
    // Interned backend name — small set repeated across all selections.
    pub name: trust_types::Symbol,
    pub role: BackendRole,
    pub can_handle: bool,
}
