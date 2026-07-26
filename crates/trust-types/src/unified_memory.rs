// trust-types/unified_memory.rs: Unified memory model for trust-wp/trust-vc cross-function proof composition
//
// trust_wp (deductive / SP-calculus) and trust_vc (ownership-aware) use
// incompatible memory models. trust_wp reasons over flat heap states with
// non-aliasing assertions; trust_vc encodes Stacked Borrows permissions,
// provenance chains, and lifetime outlives constraints.
//
// This module provides a shared memory abstraction that captures the union of
// information both backends need. Each backend can project the unified model
// into its native form. The ProofCompositionContext enables cross-function
// reasoning: if trust_wp proves function A and trust_vc proves function B, the
// composition context verifies that the memory models agree at the call
// boundary, making the combined proof sound.
//
// Part of #198: Unify trust-wp/trust-vc memory models for cross-function proof composition
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;

use serde::{Deserialize, Serialize};

use crate::SourceSpan;
use crate::provenance::{AllocationKind, BorrowKind, ProvenanceTag};

// ────────────────────────────────────────────────────────────────────────────
// MemoryRegionKind — storage class with provenance
// ────────────────────────────────────────────────────────────────────────────

/// Storage class for a memory region, with provenance tracking.
///
/// Extends `AllocationKind` with additional information about origin.
/// Stack/Heap/Static correspond to Rust's allocation categories;
/// `Projection` tracks sub-regions created by field/index access.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryRegionKind {
    /// Stack-allocated local variable with its MIR local index.
    Stack { local_index: Option<usize> },
    /// Heap-allocated storage (Box, Vec backing, etc.).
    Heap,
    /// Global or static allocation.
    Static,
    /// A sub-region of a parent region (field projection, array index, etc.).
    Projection {
        parent: RegionHandle,
        /// Offset within the parent region (if known).
        offset: Option<u64>,
    },
    /// Allocation from an unknown source (e.g., FFI return).
    Unknown,
}

impl MemoryRegionKind {
    /// Convert to the base `AllocationKind` (lossy — drops sub-region info).
    #[must_use]
    pub fn to_allocation_kind(&self) -> AllocationKind {
        match self {
            Self::Stack { .. } => AllocationKind::Stack,
            Self::Heap => AllocationKind::Heap,
            Self::Static => AllocationKind::Global,
            Self::Projection { .. } | Self::Unknown => AllocationKind::Unknown,
        }
    }

    /// Human-readable label for diagnostics.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            Self::Stack { .. } => "stack",
            Self::Heap => "heap",
            Self::Static => "static",
            Self::Projection { .. } => "projection",
            Self::Unknown => "unknown",
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// RegionHandle — lightweight region identifier
// ────────────────────────────────────────────────────────────────────────────

/// A lightweight handle identifying a memory region within a `UnifiedMemoryModel`.
///
/// This is an opaque index, not a pointer. The handle is valid only within the
/// model that issued it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RegionHandle(pub u64);

impl RegionHandle {
    /// A sentinel handle indicating no region.
    pub const NONE: Self = Self(0);

    /// Whether this is a valid (non-sentinel) handle.
    #[must_use]
    pub fn is_valid(self) -> bool {
        self.0 != 0
    }
}

impl std::fmt::Display for RegionHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "rgn_{}", self.0)
    }
}

// ────────────────────────────────────────────────────────────────────────────
// OwnershipState — Stacked Borrows permission level
// ────────────────────────────────────────────────────────────────────────────

/// Stacked Borrows permission level for a region.
///
/// Models the access a reference has over its pointee:
/// - `Owned`: full ownership, can read/write/move/drop
/// - `UniquelyBorrowed`: `&mut T`, exclusive read-write
/// - `SharedBorrowed`: `&T`, shared read-only
/// - `RawAccess`: raw pointer, read-write but weaker than `UniquelyBorrowed`
/// - `Moved`: moved out, no access
/// - `Dropped`: dropped, no access
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OwnershipState {
    /// Dropped — region has been deallocated.
    Dropped = 0,
    /// Moved out — no access permitted.
    Moved = 1,
    /// Raw pointer access (`*const T` or `*mut T`).
    RawAccess = 2,
    /// Shared immutable borrow (`&T`).
    SharedBorrowed = 3,
    /// Exclusive mutable borrow (`&mut T`).
    UniquelyBorrowed = 4,
    /// Full ownership.
    Owned = 5,
}

impl OwnershipState {
    /// Whether this state permits reads.
    #[must_use]
    pub fn permits_read(self) -> bool {
        !matches!(self, Self::Dropped | Self::Moved)
    }

    /// Whether this state permits writes.
    #[must_use]
    pub fn permits_write(self) -> bool {
        matches!(self, Self::Owned | Self::UniquelyBorrowed | Self::RawAccess)
    }

    /// Whether this state is live (not moved or dropped).
    #[must_use]
    pub fn is_live(self) -> bool {
        !matches!(self, Self::Dropped | Self::Moved)
    }

    /// Human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Owned => "owned",
            Self::UniquelyBorrowed => "uniquely borrowed",
            Self::SharedBorrowed => "shared borrowed",
            Self::RawAccess => "raw access",
            Self::Moved => "moved",
            Self::Dropped => "dropped",
        }
    }

    /// Convert from `BorrowKind` used in the provenance model.
    #[must_use]
    pub fn from_borrow_kind(kind: BorrowKind) -> Self {
        match kind {
            BorrowKind::MutableRef => Self::UniquelyBorrowed,
            BorrowKind::SharedRef => Self::SharedBorrowed,
            BorrowKind::RawMut | BorrowKind::RawShared => Self::RawAccess,
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// AliasInfo — pointer relationship tracking
// ────────────────────────────────────────────────────────────────────────────

/// Tracks aliasing relationships between pointers.
///
/// For two regions A and B, `AliasInfo` describes whether they may, must, or
/// cannot alias. This captures the combined knowledge from Rust's type system
/// (borrow checker guarantees non-aliasing for `&mut T`) and analysis results
/// (points-to analysis refines may-alias to must-alias or no-alias).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AliasRelation {
    /// The two regions definitely do not alias (disjoint storage).
    /// This is guaranteed for distinct `&mut T` borrows and for
    /// `&T` vs `&mut T` in safe Rust.
    NoAlias,
    /// The two regions may alias (conservative assumption).
    /// Used when analysis cannot determine the relationship,
    /// or for raw pointers where Rust gives no guarantees.
    MayAlias,
    /// The two regions definitely alias (same storage).
    /// Used when two references are known to point to the same location.
    MustAlias,
    /// The regions are in a parent-child relationship (one is a sub-region
    /// of the other). `child` is a projection of `parent`.
    PartialOverlap {
        /// The parent region.
        parent: RegionHandle,
        /// The child region (sub-region of parent).
        child: RegionHandle,
    },
}

/// A single alias fact: the relationship between two regions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AliasInfo {
    /// First region in the pair.
    pub region_a: RegionHandle,
    /// Second region in the pair.
    pub region_b: RegionHandle,
    /// The aliasing relationship.
    pub relation: AliasRelation,
    /// Source of this alias information (for diagnostics).
    pub source: AliasSource,
}

/// Where an alias fact came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AliasSource {
    /// Guaranteed by the Rust type system / borrow checker.
    TypeSystem,
    /// Determined by points-to analysis.
    PointsToAnalysis,
    /// Determined by provenance tracking.
    ProvenanceTracking,
    /// User-provided annotation.
    Annotation,
    /// Conservative assumption (no information available).
    Conservative,
}

impl AliasSource {
    /// Human-readable label.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            Self::TypeSystem => "type system",
            Self::PointsToAnalysis => "points-to analysis",
            Self::ProvenanceTracking => "provenance tracking",
            Self::Annotation => "annotation",
            Self::Conservative => "conservative",
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// UnifiedRegion — a memory region in the unified model
// ────────────────────────────────────────────────────────────────────────────

/// A memory region in the unified model.
///
/// Contains all information that both trust_wp (deductive) and trust_vc (ownership)
/// need to reason about memory. trust_wp uses the region identity and size for
/// non-aliasing; trust_vc additionally uses ownership, provenance, and lifetime.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnifiedRegion {
    /// Unique handle for this region.
    pub handle: RegionHandle,
    /// Storage class and provenance.
    pub kind: MemoryRegionKind,
    /// Provenance tag linking to the Stacked Borrows model.
    pub provenance: ProvenanceTag,
    /// Current ownership/permission state.
    pub ownership: OwnershipState,
    /// Size in bytes (if statically known).
    pub size_bytes: Option<u64>,
    /// Alignment in bytes.
    pub align: u32,
    /// Lexical lifetime scope depth. 0 = `'static`, higher = shorter-lived.
    pub lifetime_depth: u32,
    /// Parent region (for borrows). `None` for owned regions.
    pub borrowed_from: Option<RegionHandle>,
    /// Source location where this region was created.
    pub span: SourceSpan,
}

impl UnifiedRegion {
    /// Whether this region is live (not moved or dropped).
    #[must_use]
    pub fn is_live(&self) -> bool {
        self.ownership.is_live()
    }

    /// Whether this region permits reads.
    #[must_use]
    pub fn permits_read(&self) -> bool {
        self.ownership.permits_read()
    }

    /// Whether this region permits writes.
    #[must_use]
    pub fn permits_write(&self) -> bool {
        self.ownership.permits_write()
    }
}

// ────────────────────────────────────────────────────────────────────────────
// UnifiedMemoryModel — the shared memory abstraction
// ────────────────────────────────────────────────────────────────────────────

/// The unified memory model shared between trust_wp and trust_vc.
///
/// Stores all memory regions, their aliasing relationships, and ownership
/// information for a function being verified. Both backends can project this
/// model into their native form:
///
/// - **trust-wp projection**: flat heap with non-aliasing assertions between
///   distinct regions. Ownership/provenance information is erased.
/// - **trust-vc projection**: Stacked Borrows permissions, provenance chains,
///   lifetime outlives constraints, and non-aliasing assertions.
///
/// The model also supports cross-function composition via
/// `ProofCompositionContext`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnifiedMemoryModel {
    /// All memory regions, keyed by handle.
    regions: FxHashMap<RegionHandle, UnifiedRegion>,
    /// Alias facts between region pairs.
    alias_facts: Vec<AliasInfo>,
    /// Next handle to assign.
    next_handle: u64,
    /// The function this model describes (for diagnostics).
    pub function_name: String,
}

impl UnifiedMemoryModel {
    /// Create a new empty unified memory model for a function.
    #[must_use]
    pub fn new(function_name: impl Into<String>) -> Self {
        Self {
            regions: FxHashMap::default(),
            alias_facts: Vec::new(),
            next_handle: 1, // 0 is reserved for NONE
            function_name: function_name.into(),
        }
    }

    /// Allocate a new region, returning its handle.
    pub fn add_region(
        &mut self,
        kind: MemoryRegionKind,
        provenance: ProvenanceTag,
        ownership: OwnershipState,
        span: SourceSpan,
    ) -> RegionHandle {
        let handle = RegionHandle(self.next_handle);
        self.next_handle += 1;

        let region = UnifiedRegion {
            handle,
            kind,
            provenance,
            ownership,
            size_bytes: None,
            align: 1,
            lifetime_depth: 0,
            borrowed_from: None,
            span,
        };

        self.regions.insert(handle, region);
        handle
    }

    /// Allocate a borrow region derived from a parent.
    pub fn add_borrow(
        &mut self,
        parent: RegionHandle,
        borrow_kind: BorrowKind,
        provenance: ProvenanceTag,
        span: SourceSpan,
    ) -> Option<RegionHandle> {
        // Verify parent exists and is live.
        if !self.regions.get(&parent).is_some_and(|r| r.is_live()) {
            return None;
        }

        let handle = RegionHandle(self.next_handle);
        self.next_handle += 1;

        let parent_depth = self.regions.get(&parent).map_or(0, |r| r.lifetime_depth);

        let region = UnifiedRegion {
            handle,
            kind: MemoryRegionKind::Stack { local_index: None },
            provenance,
            ownership: OwnershipState::from_borrow_kind(borrow_kind),
            size_bytes: None,
            align: 1,
            lifetime_depth: parent_depth + 1,
            borrowed_from: Some(parent),
            span,
        };

        self.regions.insert(handle, region);

        // Add a NoAlias fact between the borrow and its parent (for &mut).
        if borrow_kind == BorrowKind::MutableRef {
            self.alias_facts.push(AliasInfo {
                region_a: parent,
                region_b: handle,
                relation: AliasRelation::NoAlias,
                source: AliasSource::TypeSystem,
            });
        }

        Some(handle)
    }

    /// Record a move: source region becomes Moved, returns a new handle for dest.
    pub fn record_move(&mut self, src: RegionHandle, span: SourceSpan) -> Option<RegionHandle> {
        let src_region = self.regions.get(&src)?;
        let kind = src_region.kind.clone();
        let provenance = src_region.provenance;

        // Mark source as moved.
        if let Some(region) = self.regions.get_mut(&src) {
            region.ownership = OwnershipState::Moved;
        }

        // Create new region for the destination.
        let handle = self.add_region(kind, provenance, OwnershipState::Owned, span);
        Some(handle)
    }

    /// Record a drop: mark the region as Dropped.
    pub fn record_drop(&mut self, handle: RegionHandle) {
        if let Some(region) = self.regions.get_mut(&handle) {
            region.ownership = OwnershipState::Dropped;
        }
    }

    /// Add an alias fact between two regions.
    pub fn add_alias_fact(&mut self, fact: AliasInfo) {
        self.alias_facts.push(fact);
    }

    /// Look up a region by handle.
    #[must_use]
    pub fn region(&self, handle: RegionHandle) -> Option<&UnifiedRegion> {
        self.regions.get(&handle)
    }

    /// Mutably look up a region by handle.
    pub fn region_mut(&mut self, handle: RegionHandle) -> Option<&mut UnifiedRegion> {
        self.regions.get_mut(&handle)
    }

    /// Get all regions.
    #[must_use]
    pub fn all_regions(&self) -> Vec<&UnifiedRegion> {
        let mut regions: Vec<_> = self.regions.values().collect();
        regions.sort_by_key(|r| r.handle);
        regions
    }

    /// Get all live (non-moved, non-dropped) regions.
    #[must_use]
    pub fn live_regions(&self) -> Vec<&UnifiedRegion> {
        let mut regions: Vec<_> = self.regions.values().filter(|r| r.is_live()).collect();
        regions.sort_by_key(|r| r.handle);
        regions
    }

    /// Get all alias facts.
    #[must_use]
    pub fn alias_facts(&self) -> &[AliasInfo] {
        &self.alias_facts
    }

    /// Number of regions.
    #[must_use]
    pub fn region_count(&self) -> usize {
        self.regions.len()
    }

    /// Number of live regions.
    #[must_use]
    pub fn live_region_count(&self) -> usize {
        self.regions.values().filter(|r| r.is_live()).count()
    }

    /// Get all borrows of a given parent region.
    #[must_use]
    pub fn borrows_of(&self, parent: RegionHandle) -> Vec<RegionHandle> {
        self.regions
            .values()
            .filter(|r| r.borrowed_from == Some(parent) && r.is_live())
            .map(|r| r.handle)
            .collect()
    }

    /// Query the alias relationship between two regions.
    ///
    /// Returns the most precise alias fact available. If no explicit fact
    /// exists, returns `MayAlias` (conservative).
    #[must_use]
    pub fn alias_between(&self, a: RegionHandle, b: RegionHandle) -> AliasRelation {
        // Check explicit facts.
        for fact in &self.alias_facts {
            if (fact.region_a == a && fact.region_b == b)
                || (fact.region_a == b && fact.region_b == a)
            {
                return fact.relation.clone();
            }
        }

        // Implicit: distinct live regions with exclusive ownership don't alias.
        if a != b {
            let a_region = self.regions.get(&a);
            let b_region = self.regions.get(&b);
            if let (Some(ar), Some(br)) = (a_region, b_region) {
                // Two UniquelyBorrowed or Owned regions are guaranteed non-aliasing
                // by the borrow checker (in safe Rust).
                if ar.is_live()
                    && br.is_live()
                    && matches!(
                        ar.ownership,
                        OwnershipState::Owned | OwnershipState::UniquelyBorrowed
                    )
                    && matches!(
                        br.ownership,
                        OwnershipState::Owned | OwnershipState::UniquelyBorrowed
                    )
                {
                    return AliasRelation::NoAlias;
                }
            }
        }

        if a == b { AliasRelation::MustAlias } else { AliasRelation::MayAlias }
    }

    /// Get the set of region handles that appear at a function boundary.
    ///
    /// Boundary regions are those that are:
    /// - Function arguments (passed in from caller)
    /// - Return values (passed back to caller)
    /// - Borrowed from a region that crosses the boundary
    #[must_use]
    pub fn boundary_regions(&self) -> Vec<RegionHandle> {
        self.regions
            .values()
            .filter(|r| {
                matches!(
                    r.kind,
                    MemoryRegionKind::Stack { local_index: Some(idx) } if idx == 0 // return slot
                ) || r.is_live() && r.borrowed_from.is_some()
            })
            .map(|r| r.handle)
            .collect()
    }
}

impl Default for UnifiedMemoryModel {
    fn default() -> Self {
        Self::new("")
    }
}

// ────────────────────────────────────────────────────────────────────────────
// ProofCompositionContext — cross-function proof reasoning
// ────────────────────────────────────────────────────────────────────────────

/// Context for composing proofs across function boundaries.
///
/// When trust_wp proves function A and trust_vc proves function B, and A calls B,
/// the composition context verifies that:
/// 1. Region identities agree at the call boundary.
/// 2. Ownership states are compatible (caller transfers, callee receives).
/// 3. Lifetime constraints are consistent (no use-after-free across boundary).
/// 4. Alias facts don't contradict across the two models.
///
/// If composition succeeds, the combined proof is sound: callee's postcondition
/// can be assumed in the caller's verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofCompositionContext {
    /// The caller's memory model (function A).
    pub caller_function: String,
    /// The callee's memory model (function B).
    pub callee_function: String,
    /// Region mappings: caller handle -> callee handle for shared regions.
    pub region_mapping: Vec<(RegionHandle, RegionHandle)>,
    /// The composition verdict.
    pub verdict: CompositionVerdict,
    /// Detailed diagnostics for each checked property.
    pub checks: Vec<CompositionCheck>,
}

/// The result of a proof composition check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CompositionVerdict {
    /// All checks pass — the composed proof is sound.
    Sound,
    /// Some checks failed — composition is unsound.
    Unsound { reasons: Vec<String> },
    /// Cannot determine soundness (e.g., missing information).
    Indeterminate { reason: String },
}

impl CompositionVerdict {
    /// Whether the composition is sound.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        matches!(self, Self::Sound)
    }
}

/// A single property checked during proof composition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompositionCheck {
    /// What property was checked.
    pub property: CompositionProperty,
    /// Whether the check passed.
    pub passed: bool,
    /// Details about the check.
    pub message: String,
}

/// Properties checked during proof composition.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CompositionProperty {
    /// Region kinds match at the boundary.
    RegionKindConsistency,
    /// Ownership transfer is valid (caller surrenders, callee acquires).
    OwnershipTransfer,
    /// No use-after-move across the boundary.
    UseAfterMoveCheck,
    /// Lifetime ordering is consistent.
    LifetimeConsistency,
    /// Alias facts don't contradict.
    AliasConsistency,
    /// Provenance chains agree.
    ProvenanceConsistency,
}

impl CompositionProperty {
    /// Human-readable label.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            Self::RegionKindConsistency => "region kind consistency",
            Self::OwnershipTransfer => "ownership transfer",
            Self::UseAfterMoveCheck => "use-after-move check",
            Self::LifetimeConsistency => "lifetime consistency",
            Self::AliasConsistency => "alias consistency",
            Self::ProvenanceConsistency => "provenance consistency",
        }
    }
}

impl ProofCompositionContext {
    /// Compose proofs from a caller and callee memory model.
    ///
    /// The `region_mapping` specifies which caller regions correspond to which
    /// callee regions (typically argument/return regions).
    #[must_use]
    pub fn compose(
        caller: &UnifiedMemoryModel,
        callee: &UnifiedMemoryModel,
        region_mapping: Vec<(RegionHandle, RegionHandle)>,
    ) -> Self {
        let mut checks = Vec::new();
        let mut failures = Vec::new();

        for &(caller_handle, callee_handle) in &region_mapping {
            let caller_region = caller.region(caller_handle);
            let callee_region = callee.region(callee_handle);

            // Check 1: Both regions must exist.
            let (cr, ce) = match (caller_region, callee_region) {
                (Some(cr), Some(ce)) => (cr, ce),
                _ => {
                    let msg = format!(
                        "region mapping {caller_handle} -> {callee_handle}: one or both regions missing"
                    );
                    checks.push(CompositionCheck {
                        property: CompositionProperty::RegionKindConsistency,
                        passed: false,
                        message: msg.clone(),
                    });
                    failures.push(msg);
                    continue;
                }
            };

            // Check 2: Region kind consistency.
            let kind_ok = cr.kind.to_allocation_kind() == ce.kind.to_allocation_kind();
            checks.push(CompositionCheck {
                property: CompositionProperty::RegionKindConsistency,
                passed: kind_ok,
                message: if kind_ok {
                    format!("{caller_handle} -> {callee_handle}: kinds match ({})", cr.kind.label())
                } else {
                    let msg = format!(
                        "{caller_handle} -> {callee_handle}: kind mismatch ({} vs {})",
                        cr.kind.label(),
                        ce.kind.label()
                    );
                    failures.push(msg.clone());
                    msg
                },
            });

            // Check 3: Use-after-move — caller must not pass moved/dropped regions.
            let move_ok = cr.is_live();
            checks.push(CompositionCheck {
                property: CompositionProperty::UseAfterMoveCheck,
                passed: move_ok,
                message: if move_ok {
                    format!("{caller_handle}: live in caller ({})", cr.ownership.label())
                } else {
                    let msg = format!(
                        "{caller_handle}: {} in caller, cannot pass to callee",
                        cr.ownership.label()
                    );
                    failures.push(msg.clone());
                    msg
                },
            });

            // Check 4: Ownership transfer soundness.
            let ownership_ok = is_valid_ownership_transfer(cr.ownership, ce.ownership);
            checks.push(CompositionCheck {
                property: CompositionProperty::OwnershipTransfer,
                passed: ownership_ok,
                message: if ownership_ok {
                    format!(
                        "{caller_handle} -> {callee_handle}: {} -> {} (valid transfer)",
                        cr.ownership.label(),
                        ce.ownership.label()
                    )
                } else {
                    let msg = format!(
                        "{caller_handle} -> {callee_handle}: {} -> {} (invalid transfer)",
                        cr.ownership.label(),
                        ce.ownership.label()
                    );
                    failures.push(msg.clone());
                    msg
                },
            });

            // Check 5: Lifetime consistency — callee's lifetime depth must be >= caller's
            // (callee cannot outlive caller for borrowed regions).
            if cr.borrowed_from.is_some() || ce.borrowed_from.is_some() {
                let lifetime_ok = ce.lifetime_depth >= cr.lifetime_depth;
                checks.push(CompositionCheck {
                    property: CompositionProperty::LifetimeConsistency,
                    passed: lifetime_ok,
                    message: if lifetime_ok {
                        format!(
                            "{caller_handle} -> {callee_handle}: lifetime depth {} >= {} (ok)",
                            ce.lifetime_depth, cr.lifetime_depth
                        )
                    } else {
                        let msg = format!(
                            "{caller_handle} -> {callee_handle}: callee lifetime {} < caller {} (invalid)",
                            ce.lifetime_depth, cr.lifetime_depth
                        );
                        failures.push(msg.clone());
                        msg
                    },
                });
            }

            // Check 6: Provenance consistency.
            let prov_ok = cr.provenance == ce.provenance
                || cr.provenance == ProvenanceTag::WILDCARD
                || ce.provenance == ProvenanceTag::WILDCARD;
            checks.push(CompositionCheck {
                property: CompositionProperty::ProvenanceConsistency,
                passed: prov_ok,
                message: if prov_ok {
                    format!(
                        "{caller_handle} -> {callee_handle}: provenance match ({} -> {})",
                        cr.provenance, ce.provenance
                    )
                } else {
                    let msg = format!(
                        "{caller_handle} -> {callee_handle}: provenance mismatch ({} vs {})",
                        cr.provenance, ce.provenance
                    );
                    failures.push(msg.clone());
                    msg
                },
            });
        }

        // Check 7: Alias consistency across the boundary.
        for &(ch1, ch2) in &region_mapping {
            for &(ch3, ch4) in &region_mapping {
                if ch1 >= ch3 {
                    continue; // avoid duplicate pairs
                }
                let caller_alias = caller.alias_between(ch1, ch3);
                let callee_alias = callee.alias_between(ch2, ch4);

                let alias_ok = are_alias_relations_compatible(&caller_alias, &callee_alias);
                checks.push(CompositionCheck {
                    property: CompositionProperty::AliasConsistency,
                    passed: alias_ok,
                    message: if alias_ok {
                        format!(
                            "alias({ch1},{ch3}) = {:?}, alias({ch2},{ch4}) = {:?}: compatible",
                            caller_alias, callee_alias
                        )
                    } else {
                        let msg = format!(
                            "alias({ch1},{ch3}) = {:?} vs alias({ch2},{ch4}) = {:?}: contradictory",
                            caller_alias, callee_alias
                        );
                        failures.push(msg.clone());
                        msg
                    },
                });
            }
        }

        let verdict = if failures.is_empty() {
            CompositionVerdict::Sound
        } else {
            CompositionVerdict::Unsound { reasons: failures }
        };

        ProofCompositionContext {
            caller_function: caller.function_name.clone(),
            callee_function: callee.function_name.clone(),
            region_mapping,
            verdict,
            checks,
        }
    }
}

/// Check whether an ownership transfer from caller to callee is valid.
///
/// Valid transfers follow Rust's ownership discipline:
/// - Owned -> Owned (move)
/// - Owned -> UniquelyBorrowed (&mut T)
/// - Owned -> SharedBorrowed (&T)
/// - UniquelyBorrowed -> UniquelyBorrowed (reborrow)
/// - UniquelyBorrowed -> SharedBorrowed (shared reborrow)
/// - SharedBorrowed -> SharedBorrowed (copy)
/// - RawAccess -> RawAccess (pointer pass)
fn is_valid_ownership_transfer(caller: OwnershipState, callee: OwnershipState) -> bool {
    match (caller, callee) {
        // Owned can transfer to anything live.
        (OwnershipState::Owned, s) => s.is_live(),
        // UniquelyBorrowed can reborrow as unique or shared.
        (OwnershipState::UniquelyBorrowed, OwnershipState::UniquelyBorrowed)
        | (OwnershipState::UniquelyBorrowed, OwnershipState::SharedBorrowed)
        | (OwnershipState::UniquelyBorrowed, OwnershipState::RawAccess) => true,
        // SharedBorrowed can only propagate as shared.
        (OwnershipState::SharedBorrowed, OwnershipState::SharedBorrowed) => true,
        // Raw access can propagate.
        (OwnershipState::RawAccess, OwnershipState::RawAccess) => true,
        // Dead states cannot transfer.
        (OwnershipState::Moved, _) | (OwnershipState::Dropped, _) => false,
        _ => false,
    }
}

/// Check whether two alias relations are compatible (non-contradictory).
fn are_alias_relations_compatible(a: &AliasRelation, b: &AliasRelation) -> bool {
    match (a, b) {
        // NoAlias vs MustAlias is a contradiction.
        (AliasRelation::NoAlias, AliasRelation::MustAlias)
        | (AliasRelation::MustAlias, AliasRelation::NoAlias) => false,
        // Everything else is compatible (MayAlias is always compatible).
        _ => true,
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helper constructors ------------------------------------------------

    fn test_span() -> SourceSpan {
        SourceSpan::default()
    }

    fn make_model(name: &str) -> UnifiedMemoryModel {
        UnifiedMemoryModel::new(name)
    }

    // -- RegionHandle tests ------------------------------------------------

    #[test]
    fn test_region_handle_none_is_invalid() {
        assert!(!RegionHandle::NONE.is_valid());
        assert!(RegionHandle(1).is_valid());
        assert!(RegionHandle(42).is_valid());
    }

    #[test]
    fn test_region_handle_display() {
        assert_eq!(format!("{}", RegionHandle(1)), "rgn_1");
        assert_eq!(format!("{}", RegionHandle(42)), "rgn_42");
    }

    #[test]
    fn test_region_handle_ordering() {
        assert!(RegionHandle(1) < RegionHandle(2));
        assert!(RegionHandle(2) > RegionHandle(1));
        assert_eq!(RegionHandle(3), RegionHandle(3));
    }

    // -- OwnershipState tests -----------------------------------------------

    #[test]
    fn test_ownership_state_permissions() {
        assert!(OwnershipState::Owned.permits_read());
        assert!(OwnershipState::Owned.permits_write());
        assert!(OwnershipState::Owned.is_live());

        assert!(OwnershipState::UniquelyBorrowed.permits_read());
        assert!(OwnershipState::UniquelyBorrowed.permits_write());
        assert!(OwnershipState::UniquelyBorrowed.is_live());

        assert!(OwnershipState::SharedBorrowed.permits_read());
        assert!(!OwnershipState::SharedBorrowed.permits_write());
        assert!(OwnershipState::SharedBorrowed.is_live());

        assert!(OwnershipState::RawAccess.permits_read());
        assert!(OwnershipState::RawAccess.permits_write());
        assert!(OwnershipState::RawAccess.is_live());

        assert!(!OwnershipState::Moved.permits_read());
        assert!(!OwnershipState::Moved.permits_write());
        assert!(!OwnershipState::Moved.is_live());

        assert!(!OwnershipState::Dropped.permits_read());
        assert!(!OwnershipState::Dropped.permits_write());
        assert!(!OwnershipState::Dropped.is_live());
    }

    #[test]
    fn test_ownership_state_ordering() {
        assert!(OwnershipState::Dropped < OwnershipState::Moved);
        assert!(OwnershipState::Moved < OwnershipState::RawAccess);
        assert!(OwnershipState::RawAccess < OwnershipState::SharedBorrowed);
        assert!(OwnershipState::SharedBorrowed < OwnershipState::UniquelyBorrowed);
        assert!(OwnershipState::UniquelyBorrowed < OwnershipState::Owned);
    }

    #[test]
    fn test_ownership_from_borrow_kind() {
        assert_eq!(
            OwnershipState::from_borrow_kind(BorrowKind::MutableRef),
            OwnershipState::UniquelyBorrowed
        );
        assert_eq!(
            OwnershipState::from_borrow_kind(BorrowKind::SharedRef),
            OwnershipState::SharedBorrowed
        );
        assert_eq!(OwnershipState::from_borrow_kind(BorrowKind::RawMut), OwnershipState::RawAccess);
        assert_eq!(
            OwnershipState::from_borrow_kind(BorrowKind::RawShared),
            OwnershipState::RawAccess
        );
    }

    #[test]
    fn test_ownership_state_labels() {
        assert_eq!(OwnershipState::Owned.label(), "owned");
        assert_eq!(OwnershipState::UniquelyBorrowed.label(), "uniquely borrowed");
        assert_eq!(OwnershipState::SharedBorrowed.label(), "shared borrowed");
        assert_eq!(OwnershipState::RawAccess.label(), "raw access");
        assert_eq!(OwnershipState::Moved.label(), "moved");
        assert_eq!(OwnershipState::Dropped.label(), "dropped");
    }

    // -- MemoryRegionKind tests ---------------------------------------------

    #[test]
    fn test_memory_region_kind_labels() {
        assert_eq!(MemoryRegionKind::Stack { local_index: None }.label(), "stack");
        assert_eq!(MemoryRegionKind::Heap.label(), "heap");
        assert_eq!(MemoryRegionKind::Static.label(), "static");
        assert_eq!(
            MemoryRegionKind::Projection { parent: RegionHandle(1), offset: None }.label(),
            "projection"
        );
        assert_eq!(MemoryRegionKind::Unknown.label(), "unknown");
    }

    #[test]
    fn test_memory_region_kind_to_allocation_kind() {
        assert_eq!(
            MemoryRegionKind::Stack { local_index: Some(0) }.to_allocation_kind(),
            AllocationKind::Stack
        );
        assert_eq!(MemoryRegionKind::Heap.to_allocation_kind(), AllocationKind::Heap);
        assert_eq!(MemoryRegionKind::Static.to_allocation_kind(), AllocationKind::Global);
        assert_eq!(MemoryRegionKind::Unknown.to_allocation_kind(), AllocationKind::Unknown);
    }

    // -- AliasRelation tests ------------------------------------------------

    #[test]
    fn test_alias_source_labels() {
        assert_eq!(AliasSource::TypeSystem.label(), "type system");
        assert_eq!(AliasSource::PointsToAnalysis.label(), "points-to analysis");
        assert_eq!(AliasSource::ProvenanceTracking.label(), "provenance tracking");
        assert_eq!(AliasSource::Annotation.label(), "annotation");
        assert_eq!(AliasSource::Conservative.label(), "conservative");
    }

    // -- UnifiedMemoryModel basic operations --------------------------------

    #[test]
    fn test_empty_model() {
        let model = make_model("test_fn");
        assert_eq!(model.region_count(), 0);
        assert_eq!(model.live_region_count(), 0);
        assert!(model.all_regions().is_empty());
        assert!(model.live_regions().is_empty());
        assert!(model.alias_facts().is_empty());
        assert_eq!(model.function_name, "test_fn");
    }

    #[test]
    fn test_add_region() {
        let mut model = make_model("test_fn");
        let h1 = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let h2 = model.add_region(
            MemoryRegionKind::Heap,
            ProvenanceTag(2),
            OwnershipState::Owned,
            test_span(),
        );

        assert_ne!(h1, h2);
        assert_eq!(model.region_count(), 2);
        assert_eq!(model.live_region_count(), 2);

        let r1 = model.region(h1).expect("region 1");
        assert_eq!(r1.handle, h1);
        assert_eq!(r1.provenance, ProvenanceTag(1));
        assert_eq!(r1.ownership, OwnershipState::Owned);
        assert!(r1.is_live());

        let r2 = model.region(h2).expect("region 2");
        assert!(matches!(r2.kind, MemoryRegionKind::Heap));
    }

    #[test]
    fn test_add_borrow() {
        let mut model = make_model("test_fn");
        let parent = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let borrow = model
            .add_borrow(parent, BorrowKind::MutableRef, ProvenanceTag(2), test_span())
            .expect("should succeed");

        assert_eq!(model.region_count(), 2);
        let br = model.region(borrow).expect("borrow region");
        assert_eq!(br.ownership, OwnershipState::UniquelyBorrowed);
        assert_eq!(br.borrowed_from, Some(parent));
        assert_eq!(br.lifetime_depth, 1);

        // NoAlias fact should have been added for &mut.
        assert_eq!(model.alias_facts().len(), 1);
        assert_eq!(model.alias_facts()[0].relation, AliasRelation::NoAlias);
    }

    #[test]
    fn test_add_shared_borrow() {
        let mut model = make_model("test_fn");
        let parent = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let borrow = model
            .add_borrow(parent, BorrowKind::SharedRef, ProvenanceTag(2), test_span())
            .expect("should succeed");

        let br = model.region(borrow).expect("borrow region");
        assert_eq!(br.ownership, OwnershipState::SharedBorrowed);
        // Shared borrows don't add NoAlias facts.
        assert!(model.alias_facts().is_empty());
    }

    #[test]
    fn test_borrow_from_moved_fails() {
        let mut model = make_model("test_fn");
        let parent = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        model.record_move(parent, test_span());

        let result = model.add_borrow(parent, BorrowKind::SharedRef, ProvenanceTag(2), test_span());
        assert!(result.is_none(), "cannot borrow from moved region");
    }

    #[test]
    fn test_record_move() {
        let mut model = make_model("test_fn");
        let h = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let new_h = model.record_move(h, test_span()).expect("move should succeed");

        // Original is moved.
        let orig = model.region(h).expect("original region");
        assert_eq!(orig.ownership, OwnershipState::Moved);
        assert!(!orig.is_live());

        // New region is owned.
        let new_r = model.region(new_h).expect("new region");
        assert_eq!(new_r.ownership, OwnershipState::Owned);
        assert!(new_r.is_live());

        assert_eq!(model.region_count(), 2);
        assert_eq!(model.live_region_count(), 1);
    }

    #[test]
    fn test_record_drop() {
        let mut model = make_model("test_fn");
        let h = model.add_region(
            MemoryRegionKind::Heap,
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        model.record_drop(h);

        let r = model.region(h).expect("region");
        assert_eq!(r.ownership, OwnershipState::Dropped);
        assert!(!r.is_live());
        assert_eq!(model.live_region_count(), 0);
    }

    #[test]
    fn test_borrows_of() {
        let mut model = make_model("test_fn");
        let parent = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let b1 = model
            .add_borrow(parent, BorrowKind::SharedRef, ProvenanceTag(2), test_span())
            .expect("borrow 1");
        let b2 = model
            .add_borrow(parent, BorrowKind::SharedRef, ProvenanceTag(3), test_span())
            .expect("borrow 2");

        let borrows = model.borrows_of(parent);
        assert_eq!(borrows.len(), 2);
        assert!(borrows.contains(&b1));
        assert!(borrows.contains(&b2));
    }

    // -- Alias query tests --------------------------------------------------

    #[test]
    fn test_alias_self_is_must_alias() {
        let mut model = make_model("test_fn");
        let h = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        assert_eq!(model.alias_between(h, h), AliasRelation::MustAlias);
    }

    #[test]
    fn test_alias_distinct_owned_is_no_alias() {
        let mut model = make_model("test_fn");
        let h1 = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let h2 = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(2),
            OwnershipState::Owned,
            test_span(),
        );

        assert_eq!(model.alias_between(h1, h2), AliasRelation::NoAlias);
    }

    #[test]
    fn test_alias_shared_borrows_may_alias() {
        let mut model = make_model("test_fn");
        let parent = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let b1 = model
            .add_borrow(parent, BorrowKind::SharedRef, ProvenanceTag(2), test_span())
            .expect("borrow 1");
        let b2 = model
            .add_borrow(parent, BorrowKind::SharedRef, ProvenanceTag(3), test_span())
            .expect("borrow 2");

        // Two shared borrows of the same parent may alias.
        assert_eq!(model.alias_between(b1, b2), AliasRelation::MayAlias);
    }

    #[test]
    fn test_alias_explicit_fact_overrides_default() {
        let mut model = make_model("test_fn");
        let h1 = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::SharedBorrowed,
            test_span(),
        );
        let h2 = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(2),
            OwnershipState::SharedBorrowed,
            test_span(),
        );

        // Default would be MayAlias for shared borrows.
        assert_eq!(model.alias_between(h1, h2), AliasRelation::MayAlias);

        // Add explicit NoAlias fact.
        model.add_alias_fact(AliasInfo {
            region_a: h1,
            region_b: h2,
            relation: AliasRelation::NoAlias,
            source: AliasSource::PointsToAnalysis,
        });

        assert_eq!(model.alias_between(h1, h2), AliasRelation::NoAlias);
    }

    // -- ProofCompositionContext tests: sound composition --------------------

    #[test]
    fn test_compose_matching_owned_regions_is_sound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(ctx.verdict.is_sound(), "matching owned regions should compose soundly");
        assert_eq!(ctx.caller_function, "caller");
        assert_eq!(ctx.callee_function, "callee");
    }

    #[test]
    fn test_compose_owned_to_borrowed_is_sound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::UniquelyBorrowed,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(ctx.verdict.is_sound(), "owned -> uniquely_borrowed is a valid transfer");
    }

    #[test]
    fn test_compose_disjoint_regions_is_sound() {
        let caller = make_model("caller");
        let callee = make_model("callee");

        // No shared regions — trivially sound.
        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![]);
        assert!(ctx.verdict.is_sound());
    }

    #[test]
    fn test_compose_shared_to_shared_is_sound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::SharedBorrowed,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::SharedBorrowed,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(ctx.verdict.is_sound(), "shared -> shared is valid");
    }

    // -- ProofCompositionContext tests: unsound composition ------------------

    #[test]
    fn test_compose_moved_to_live_is_unsound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Moved,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(!ctx.verdict.is_sound(), "moved -> owned should be unsound");
    }

    #[test]
    fn test_compose_kind_mismatch_is_unsound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Heap,
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(!ctx.verdict.is_sound(), "stack vs heap kind mismatch should be unsound");
    }

    #[test]
    fn test_compose_provenance_mismatch_is_unsound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(99),
            OwnershipState::Owned,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(!ctx.verdict.is_sound(), "provenance mismatch should be unsound");
    }

    #[test]
    fn test_compose_shared_to_unique_is_unsound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::SharedBorrowed,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::UniquelyBorrowed,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(
            !ctx.verdict.is_sound(),
            "shared_borrowed -> uniquely_borrowed is not a valid transfer"
        );
    }

    #[test]
    fn test_compose_alias_contradiction_is_unsound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let c2 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(2) },
            ProvenanceTag(2),
            OwnershipState::Owned,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let e2 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(2) },
            ProvenanceTag(2),
            OwnershipState::Owned,
            test_span(),
        );
        // Add a MustAlias fact in callee that contradicts caller's NoAlias.
        callee.add_alias_fact(AliasInfo {
            region_a: e1,
            region_b: e2,
            relation: AliasRelation::MustAlias,
            source: AliasSource::Annotation,
        });

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1), (c2, e2)]);
        assert!(
            !ctx.verdict.is_sound(),
            "NoAlias in caller vs MustAlias in callee should be unsound"
        );
    }

    // -- ProofCompositionContext: wildcard provenance -----------------------

    #[test]
    fn test_compose_wildcard_provenance_is_compatible() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag::WILDCARD,
            OwnershipState::Owned,
            test_span(),
        );

        let mut callee = make_model("callee");
        let e1 = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(42),
            OwnershipState::Owned,
            test_span(),
        );

        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, e1)]);
        assert!(ctx.verdict.is_sound(), "wildcard provenance should match any tag");
    }

    // -- ProofCompositionContext: missing regions ---------------------------

    #[test]
    fn test_compose_missing_callee_region_is_unsound() {
        let mut caller = make_model("caller");
        let c1 = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        let callee = make_model("callee");
        // Callee has no regions, but mapping references a callee handle.
        let ctx = ProofCompositionContext::compose(&caller, &callee, vec![(c1, RegionHandle(99))]);
        assert!(!ctx.verdict.is_sound(), "missing callee region should be unsound");
    }

    // -- ProofCompositionContext: complex multi-region composition ----------

    #[test]
    fn test_compose_complex_borrow_chain() {
        // Caller: owned x, &mut y from x, &z from x
        let mut caller = make_model("caller");
        let cx = caller.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let cy = caller
            .add_borrow(cx, BorrowKind::MutableRef, ProvenanceTag(2), test_span())
            .expect("mut borrow");
        let cz = caller
            .add_borrow(cx, BorrowKind::SharedRef, ProvenanceTag(3), test_span())
            .expect("shared borrow");

        // Callee: receives the same borrow chain.
        let mut callee = make_model("callee");
        let ex = callee.add_region(
            MemoryRegionKind::Stack { local_index: Some(1) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );
        let ey = callee
            .add_borrow(ex, BorrowKind::MutableRef, ProvenanceTag(2), test_span())
            .expect("mut borrow");
        let ez = callee
            .add_borrow(ex, BorrowKind::SharedRef, ProvenanceTag(3), test_span())
            .expect("shared borrow");

        let ctx =
            ProofCompositionContext::compose(&caller, &callee, vec![(cx, ex), (cy, ey), (cz, ez)]);
        assert!(ctx.verdict.is_sound(), "matching borrow chains should compose soundly");
        // Should have checks for all 3 region pairs.
        assert!(!ctx.checks.is_empty());
    }

    // -- Ownership transfer validation -------------------------------------

    #[test]
    fn test_valid_ownership_transfers() {
        // Owned -> anything live
        assert!(is_valid_ownership_transfer(OwnershipState::Owned, OwnershipState::Owned));
        assert!(is_valid_ownership_transfer(
            OwnershipState::Owned,
            OwnershipState::UniquelyBorrowed
        ));
        assert!(is_valid_ownership_transfer(OwnershipState::Owned, OwnershipState::SharedBorrowed));
        assert!(is_valid_ownership_transfer(OwnershipState::Owned, OwnershipState::RawAccess));

        // UniquelyBorrowed reborrows
        assert!(is_valid_ownership_transfer(
            OwnershipState::UniquelyBorrowed,
            OwnershipState::UniquelyBorrowed
        ));
        assert!(is_valid_ownership_transfer(
            OwnershipState::UniquelyBorrowed,
            OwnershipState::SharedBorrowed
        ));
        assert!(is_valid_ownership_transfer(
            OwnershipState::UniquelyBorrowed,
            OwnershipState::RawAccess
        ));

        // SharedBorrowed -> SharedBorrowed
        assert!(is_valid_ownership_transfer(
            OwnershipState::SharedBorrowed,
            OwnershipState::SharedBorrowed
        ));

        // Raw -> Raw
        assert!(is_valid_ownership_transfer(OwnershipState::RawAccess, OwnershipState::RawAccess));
    }

    #[test]
    fn test_invalid_ownership_transfers() {
        // Moved/Dropped cannot transfer.
        assert!(!is_valid_ownership_transfer(OwnershipState::Moved, OwnershipState::Owned));
        assert!(!is_valid_ownership_transfer(OwnershipState::Dropped, OwnershipState::Owned));

        // SharedBorrowed cannot escalate to UniquelyBorrowed.
        assert!(!is_valid_ownership_transfer(
            OwnershipState::SharedBorrowed,
            OwnershipState::UniquelyBorrowed
        ));

        // RawAccess cannot escalate to Owned.
        assert!(!is_valid_ownership_transfer(OwnershipState::RawAccess, OwnershipState::Owned));

        // Owned cannot transfer to dead states.
        assert!(!is_valid_ownership_transfer(OwnershipState::Owned, OwnershipState::Moved));
        assert!(!is_valid_ownership_transfer(OwnershipState::Owned, OwnershipState::Dropped));
    }

    // -- Alias compatibility -----------------------------------------------

    #[test]
    fn test_alias_relations_compatible() {
        assert!(are_alias_relations_compatible(&AliasRelation::NoAlias, &AliasRelation::NoAlias));
        assert!(are_alias_relations_compatible(
            &AliasRelation::MustAlias,
            &AliasRelation::MustAlias
        ));
        assert!(are_alias_relations_compatible(&AliasRelation::MayAlias, &AliasRelation::NoAlias));
        assert!(are_alias_relations_compatible(
            &AliasRelation::MayAlias,
            &AliasRelation::MustAlias
        ));
    }

    #[test]
    fn test_alias_relations_incompatible() {
        assert!(!are_alias_relations_compatible(
            &AliasRelation::NoAlias,
            &AliasRelation::MustAlias
        ));
        assert!(!are_alias_relations_compatible(
            &AliasRelation::MustAlias,
            &AliasRelation::NoAlias
        ));
    }

    // -- Serialization roundtrip -------------------------------------------

    #[test]
    fn test_ownership_state_serialization_roundtrip() {
        for state in [
            OwnershipState::Owned,
            OwnershipState::UniquelyBorrowed,
            OwnershipState::SharedBorrowed,
            OwnershipState::RawAccess,
            OwnershipState::Moved,
            OwnershipState::Dropped,
        ] {
            let json = serde_json::to_string(&state).expect("serialize");
            let round: OwnershipState = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(round, state);
        }
    }

    #[test]
    fn test_region_handle_serialization_roundtrip() {
        let handle = RegionHandle(42);
        let json = serde_json::to_string(&handle).expect("serialize");
        let round: RegionHandle = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, handle);
    }

    #[test]
    fn test_unified_region_serialization_roundtrip() {
        let region = UnifiedRegion {
            handle: RegionHandle(1),
            kind: MemoryRegionKind::Heap,
            provenance: ProvenanceTag(42),
            ownership: OwnershipState::Owned,
            size_bytes: Some(64),
            align: 8,
            lifetime_depth: 0,
            borrowed_from: None,
            span: SourceSpan::default(),
        };

        let json = serde_json::to_string(&region).expect("serialize");
        let round: UnifiedRegion = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.handle, RegionHandle(1));
        assert_eq!(round.provenance, ProvenanceTag(42));
        assert_eq!(round.ownership, OwnershipState::Owned);
        assert_eq!(round.size_bytes, Some(64));
    }

    #[test]
    fn test_composition_verdict_serialization_roundtrip() {
        let v1 = CompositionVerdict::Sound;
        let json = serde_json::to_string(&v1).expect("serialize");
        let round: CompositionVerdict = serde_json::from_str(&json).expect("deserialize");
        assert!(round.is_sound());

        let v2 = CompositionVerdict::Unsound { reasons: vec!["kind mismatch".to_string()] };
        let json = serde_json::to_string(&v2).expect("serialize");
        let round: CompositionVerdict = serde_json::from_str(&json).expect("deserialize");
        assert!(!round.is_sound());
    }

    // -- region_mut tests ---------------------------------------------------

    #[test]
    fn test_region_mut_updates() {
        let mut model = make_model("test_fn");
        let h = model.add_region(
            MemoryRegionKind::Stack { local_index: Some(0) },
            ProvenanceTag(1),
            OwnershipState::Owned,
            test_span(),
        );

        // Update size and alignment.
        if let Some(r) = model.region_mut(h) {
            r.size_bytes = Some(128);
            r.align = 16;
        }

        let r = model.region(h).expect("region");
        assert_eq!(r.size_bytes, Some(128));
        assert_eq!(r.align, 16);
    }

    // -- Composition property labels ----------------------------------------

    #[test]
    fn test_composition_property_labels() {
        assert_eq!(CompositionProperty::RegionKindConsistency.label(), "region kind consistency");
        assert_eq!(CompositionProperty::OwnershipTransfer.label(), "ownership transfer");
        assert_eq!(CompositionProperty::UseAfterMoveCheck.label(), "use-after-move check");
        assert_eq!(CompositionProperty::LifetimeConsistency.label(), "lifetime consistency");
        assert_eq!(CompositionProperty::AliasConsistency.label(), "alias consistency");
        assert_eq!(CompositionProperty::ProvenanceConsistency.label(), "provenance consistency");
    }
}
