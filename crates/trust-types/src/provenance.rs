// trust-types/provenance.rs: Provenance tracking types for memory model Layer 2
//
// Models pointer provenance (allocation origin, borrow chain) for verifying
// Stacked Borrows / Tree Borrows rules as verification conditions. These types
// are consumed by trust_vcgen/memory_provenance.rs to generate VCs.
//
// Part of #150: Memory model Layers 2-3
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::SourceSpan;

// ────────────────────────────────────────────────────────────────────────────
// Provenance tags and chains
// ────────────────────────────────────────────────────────────────────────────

/// Unique tag identifying a pointer's provenance (allocation origin).
///
/// Every allocation produces a fresh tag. Borrows derive child tags from
/// their parent. Two pointers with different tags must not alias unless
/// one is a descendant of the other in the borrow tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProvenanceTag(pub u64);

impl ProvenanceTag {
    /// The wildcard tag that matches any provenance (used for `expose_provenance`).
    pub const WILDCARD: Self = Self(0);

    /// Whether this is a concrete (non-wildcard) provenance tag.
    #[must_use]
    pub fn is_concrete(self) -> bool {
        self.0 != 0
    }
}

impl std::fmt::Display for ProvenanceTag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == 0 { write!(f, "prov(*)") } else { write!(f, "prov({})", self.0) }
    }
}

/// Kind of borrow: shared, mutable, or raw pointer.
///
/// Determines permission level in the Stacked Borrows model:
/// - SharedRef: read-only, multiple allowed
/// - MutableRef: exclusive read-write
/// - RawShared: raw `*const T`, read access
/// - RawMut: raw `*mut T`, read-write access (weaker than MutableRef)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BorrowKind {
    /// `&T` -- shared immutable borrow.
    SharedRef,
    /// `&mut T` -- exclusive mutable borrow.
    MutableRef,
    /// `*const T` -- raw shared pointer.
    RawShared,
    /// `*mut T` -- raw mutable pointer.
    RawMut,
}

impl BorrowKind {
    /// Whether this borrow kind permits writes.
    #[must_use]
    pub fn permits_write(self) -> bool {
        matches!(self, Self::MutableRef | Self::RawMut)
    }

    /// Whether this borrow kind permits reads.
    #[must_use]
    pub fn permits_read(self) -> bool {
        true // all borrow kinds permit reads
    }

    /// Human-readable label for diagnostics.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::SharedRef => "&T",
            Self::MutableRef => "&mut T",
            Self::RawShared => "*const T",
            Self::RawMut => "*mut T",
        }
    }
}

/// A single entry in the borrow stack (Stacked Borrows model).
///
/// Each entry records which tag has what kind of access to a memory location.
/// The stack enforces ordering: a use of a tag invalidates all entries above it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BorrowEntry {
    /// The provenance tag for this borrow.
    pub tag: ProvenanceTag,
    /// What kind of access this borrow grants.
    pub kind: BorrowKind,
    /// Where this borrow was created.
    pub span: SourceSpan,
}

/// Chain of borrows from allocation root to current pointer.
///
/// Tracks the derivation path: allocation -> &T -> &mut T -> *mut T etc.
/// Used to verify that pointer accesses respect the borrow hierarchy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenanceChain {
    /// The root allocation tag.
    pub root: ProvenanceTag,
    /// Ordered sequence of borrow derivations from root to tip.
    pub entries: Vec<BorrowEntry>,
}

impl ProvenanceChain {
    /// Create a new chain starting from a root allocation.
    #[must_use]
    pub fn new(root: ProvenanceTag) -> Self {
        Self { root, entries: Vec::new() }
    }

    /// Push a new borrow onto the chain.
    pub fn push(&mut self, entry: BorrowEntry) {
        self.entries.push(entry);
    }

    /// The current (most recent) provenance tag.
    #[must_use]
    pub fn current_tag(&self) -> ProvenanceTag {
        self.entries.last().map_or(self.root, |e| e.tag)
    }

    /// Number of borrow steps from root to current.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.entries.len()
    }

    /// Whether a given tag appears anywhere in this chain.
    #[must_use]
    pub fn contains_tag(&self, tag: ProvenanceTag) -> bool {
        self.root == tag || self.entries.iter().any(|e| e.tag == tag)
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Memory regions
// ────────────────────────────────────────────────────────────────────────────

/// A memory region tracked by the provenance model.
///
/// Each allocation (stack, heap, global) is a distinct region with a unique
/// provenance tag. Pointers derived from a region carry its tag.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryRegion {
    /// Unique provenance tag for this region.
    pub tag: ProvenanceTag,
    /// Where this region was allocated.
    pub alloc_span: SourceSpan,
    /// Kind of allocation.
    pub kind: AllocationKind,
    /// Size in bytes (if known statically).
    pub size: Option<u64>,
    /// Alignment in bytes.
    pub align: u32,
    /// Whether this region has been deallocated.
    pub freed: bool,
}

impl MemoryRegion {
    /// Whether this region is still live (not freed).
    #[must_use]
    pub fn is_live(&self) -> bool {
        !self.freed
    }

    /// Mark this region as freed.
    pub fn free(&mut self) {
        self.freed = true;
    }
}

/// Kind of memory allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AllocationKind {
    /// Stack-allocated local variable.
    Stack,
    /// Heap allocation (Box, Vec backing, etc.).
    Heap,
    /// Global/static allocation.
    Global,
    /// Allocation from an unknown source (e.g., FFI return).
    Unknown,
}

impl AllocationKind {
    /// Human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Stack => "stack",
            Self::Heap => "heap",
            Self::Global => "global",
            Self::Unknown => "unknown",
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Provenance violations
// ────────────────────────────────────────────────────────────────────────────

/// A provenance violation detected during analysis.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenanceViolation {
    /// What rule was violated.
    pub kind: ProvenanceViolationKind,
    /// The pointer tag that caused the violation.
    pub tag: ProvenanceTag,
    /// Where in the source code.
    pub span: SourceSpan,
    /// Human-readable description.
    pub message: String,
}

/// Kinds of provenance violations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProvenanceViolationKind {
    /// Accessing memory through a pointer whose tag is no longer valid
    /// (popped from the borrow stack).
    InvalidatedBorrow,
    /// Writing through a shared reference.
    WriteThroughSharedRef,
    /// Using a pointer after the allocation was freed.
    UseAfterFree,
    /// Accessing memory through a pointer with the wrong provenance
    /// (not derived from the region's allocation).
    ProvenanceMismatch,
    /// Reading through a pointer that was created with write-only intent
    /// (not applicable in standard Rust, but modeled for completeness).
    PermissionDenied,
    /// Accessing out of bounds within a region.
    OutOfBoundsAccess,
}

impl ProvenanceViolationKind {
    /// Human-readable label.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            Self::InvalidatedBorrow => "invalidated borrow",
            Self::WriteThroughSharedRef => "write through shared ref",
            Self::UseAfterFree => "use after free",
            Self::ProvenanceMismatch => "provenance mismatch",
            Self::PermissionDenied => "permission denied",
            Self::OutOfBoundsAccess => "out of bounds access",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_provenance_tag_wildcard() {
        assert!(!ProvenanceTag::WILDCARD.is_concrete());
        assert!(ProvenanceTag(1).is_concrete());
        assert!(ProvenanceTag(42).is_concrete());
    }

    #[test]
    fn test_provenance_tag_display() {
        assert_eq!(format!("{}", ProvenanceTag::WILDCARD), "prov(*)");
        assert_eq!(format!("{}", ProvenanceTag(7)), "prov(7)");
    }

    #[test]
    fn test_borrow_kind_permissions() {
        assert!(!BorrowKind::SharedRef.permits_write());
        assert!(BorrowKind::SharedRef.permits_read());

        assert!(BorrowKind::MutableRef.permits_write());
        assert!(BorrowKind::MutableRef.permits_read());

        assert!(!BorrowKind::RawShared.permits_write());
        assert!(BorrowKind::RawShared.permits_read());

        assert!(BorrowKind::RawMut.permits_write());
        assert!(BorrowKind::RawMut.permits_read());
    }

    #[test]
    fn test_borrow_kind_labels() {
        assert_eq!(BorrowKind::SharedRef.label(), "&T");
        assert_eq!(BorrowKind::MutableRef.label(), "&mut T");
        assert_eq!(BorrowKind::RawShared.label(), "*const T");
        assert_eq!(BorrowKind::RawMut.label(), "*mut T");
    }

    #[test]
    fn test_provenance_chain_new() {
        let chain = ProvenanceChain::new(ProvenanceTag(1));
        assert_eq!(chain.root, ProvenanceTag(1));
        assert_eq!(chain.depth(), 0);
        assert_eq!(chain.current_tag(), ProvenanceTag(1));
        assert!(chain.contains_tag(ProvenanceTag(1)));
        assert!(!chain.contains_tag(ProvenanceTag(2)));
    }

    #[test]
    fn test_provenance_chain_push() {
        let mut chain = ProvenanceChain::new(ProvenanceTag(1));
        chain.push(BorrowEntry {
            tag: ProvenanceTag(2),
            kind: BorrowKind::SharedRef,
            span: SourceSpan::default(),
        });
        chain.push(BorrowEntry {
            tag: ProvenanceTag(3),
            kind: BorrowKind::MutableRef,
            span: SourceSpan::default(),
        });

        assert_eq!(chain.depth(), 2);
        assert_eq!(chain.current_tag(), ProvenanceTag(3));
        assert!(chain.contains_tag(ProvenanceTag(1)));
        assert!(chain.contains_tag(ProvenanceTag(2)));
        assert!(chain.contains_tag(ProvenanceTag(3)));
        assert!(!chain.contains_tag(ProvenanceTag(4)));
    }

    #[test]
    fn test_memory_region_lifecycle() {
        let mut region = MemoryRegion {
            tag: ProvenanceTag(10),
            alloc_span: SourceSpan::default(),
            kind: AllocationKind::Heap,
            size: Some(64),
            align: 8,
            freed: false,
        };

        assert!(region.is_live());
        region.free();
        assert!(!region.is_live());
    }

    #[test]
    fn test_allocation_kind_labels() {
        assert_eq!(AllocationKind::Stack.label(), "stack");
        assert_eq!(AllocationKind::Heap.label(), "heap");
        assert_eq!(AllocationKind::Global.label(), "global");
        assert_eq!(AllocationKind::Unknown.label(), "unknown");
    }

    #[test]
    fn test_provenance_violation_kind_labels() {
        assert_eq!(ProvenanceViolationKind::InvalidatedBorrow.label(), "invalidated borrow");
        assert_eq!(
            ProvenanceViolationKind::WriteThroughSharedRef.label(),
            "write through shared ref"
        );
        assert_eq!(ProvenanceViolationKind::UseAfterFree.label(), "use after free");
        assert_eq!(ProvenanceViolationKind::ProvenanceMismatch.label(), "provenance mismatch");
        assert_eq!(ProvenanceViolationKind::PermissionDenied.label(), "permission denied");
        assert_eq!(ProvenanceViolationKind::OutOfBoundsAccess.label(), "out of bounds access");
    }

    #[test]
    fn test_provenance_tag_serialization_roundtrip() {
        let tag = ProvenanceTag(42);
        let json = serde_json::to_string(&tag).expect("serialize");
        let round: ProvenanceTag = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, tag);
    }

    #[test]
    fn test_borrow_kind_serialization_roundtrip() {
        for kind in [
            BorrowKind::SharedRef,
            BorrowKind::MutableRef,
            BorrowKind::RawShared,
            BorrowKind::RawMut,
        ] {
            let json = serde_json::to_string(&kind).expect("serialize");
            let round: BorrowKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(round, kind);
        }
    }

    #[test]
    fn test_provenance_chain_serialization_roundtrip() {
        let mut chain = ProvenanceChain::new(ProvenanceTag(1));
        chain.push(BorrowEntry {
            tag: ProvenanceTag(2),
            kind: BorrowKind::MutableRef,
            span: SourceSpan::default(),
        });

        let json = serde_json::to_string(&chain).expect("serialize");
        let round: ProvenanceChain = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.root, chain.root);
        assert_eq!(round.entries.len(), 1);
        assert_eq!(round.entries[0].tag, ProvenanceTag(2));
    }

    #[test]
    fn test_memory_region_serialization_roundtrip() {
        let region = MemoryRegion {
            tag: ProvenanceTag(5),
            alloc_span: SourceSpan::default(),
            kind: AllocationKind::Stack,
            size: Some(32),
            align: 4,
            freed: false,
        };

        let json = serde_json::to_string(&region).expect("serialize");
        let round: MemoryRegion = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.tag, ProvenanceTag(5));
        assert_eq!(round.kind, AllocationKind::Stack);
        assert_eq!(round.size, Some(32));
        assert_eq!(round.align, 4);
        assert!(!round.freed);
    }

    #[test]
    fn test_provenance_violation_serialization_roundtrip() {
        let violation = ProvenanceViolation {
            kind: ProvenanceViolationKind::InvalidatedBorrow,
            tag: ProvenanceTag(3),
            span: SourceSpan::default(),
            message: "borrow was invalidated by a mutable reborrow".into(),
        };

        let json = serde_json::to_string(&violation).expect("serialize");
        let round: ProvenanceViolation = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.kind, ProvenanceViolationKind::InvalidatedBorrow);
        assert_eq!(round.tag, ProvenanceTag(3));
    }
}
