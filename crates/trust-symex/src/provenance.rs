// trust-symex provenance tracking (Layer 2)
//
// Tracks pointer provenance as ghost state for unsafe Rust verification.
// Each allocation gets a unique `ProvenanceTag`. Pointer arithmetic and
// casts must preserve provenance within the originating allocation.
// Models Stacked Borrows / Tree Borrows as a borrow stack per allocation.
//
// Design: Issue #150, VISION.md Section 9 (Memory Abstraction)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::Formula;

use crate::region::RegionId;

// ---------------------------------------------------------------------------
// Provenance tag
// ---------------------------------------------------------------------------

/// Unique identity for a memory allocation.
///
/// Every `alloc`, `Box::new`, stack frame, or static gets a unique tag.
/// Pointer arithmetic must stay within the allocation identified by its tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ProvenanceTag(u64);

impl ProvenanceTag {
    /// Create a tag from a raw id (for testing / deserialization).
    #[must_use]
    pub fn from_raw(id: u64) -> Self {
        Self(id)
    }

    /// Returns the underlying numeric id.
    #[must_use]
    pub fn as_raw(self) -> u64 {
        self.0
    }
}

impl std::fmt::Display for ProvenanceTag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "prov#{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// Borrow permission levels (Stacked Borrows)
// ---------------------------------------------------------------------------

/// Permission level on the borrow stack, following the Stacked Borrows model.
///
/// Ref: R. Jung et al., "Stacked Borrows: An Aliasing Model for Rust", 2020.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Permission {
    /// Full read/write access (`&mut T` or owned).
    Unique,
    /// Read-only shared access (`&T`).
    SharedReadOnly,
    /// Write access through `UnsafeCell` interior mutability.
    SharedReadWrite,
    /// Disabled -- tag has been popped from the stack.
    Disabled,
}

impl std::fmt::Display for Permission {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unique => write!(f, "Unique"),
            Self::SharedReadOnly => write!(f, "SharedReadOnly"),
            Self::SharedReadWrite => write!(f, "SharedReadWrite"),
            Self::Disabled => write!(f, "Disabled"),
        }
    }
}

// ---------------------------------------------------------------------------
// Borrow stack item
// ---------------------------------------------------------------------------

/// An entry on the borrow stack for an allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BorrowStackItem {
    /// The tag identifying this borrow.
    pub tag: ProvenanceTag,
    /// The permission level of this borrow.
    pub permission: Permission,
}

// ---------------------------------------------------------------------------
// Allocation metadata
// ---------------------------------------------------------------------------

/// Metadata for a single allocation tracked by the provenance model.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AllocationInfo {
    /// Provenance tag of this allocation.
    tag: ProvenanceTag,
    /// Size in bytes (0 for ZSTs).
    size: u64,
    /// Whether the allocation is still live (not freed).
    live: bool,
    /// The borrow stack for this allocation (Stacked Borrows model).
    /// Top of stack is last element.
    borrow_stack: Vec<BorrowStackItem>,
    /// Optional link to the Layer 1 region.
    region_id: Option<RegionId>,
}

impl AllocationInfo {
    /// Returns the provenance tag.
    #[must_use]
    pub fn tag(&self) -> ProvenanceTag {
        self.tag
    }

    /// Returns the allocation size in bytes.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Returns whether the allocation is still live.
    #[must_use]
    pub fn is_live(&self) -> bool {
        self.live
    }

    /// Returns the borrow stack (bottom to top).
    #[must_use]
    pub fn borrow_stack(&self) -> &[BorrowStackItem] {
        &self.borrow_stack
    }

    /// Returns the linked region id, if any.
    #[must_use]
    pub fn region_id(&self) -> Option<RegionId> {
        self.region_id
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from provenance-checking operations.
#[derive(Debug, Clone, Error, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProvenanceError {
    #[error("unknown provenance tag {tag}")]
    UnknownTag { tag: ProvenanceTag },

    #[error("use after free: allocation {tag} was freed")]
    UseAfterFree { tag: ProvenanceTag },

    #[error("double free: allocation {tag} was already freed")]
    DoubleFree { tag: ProvenanceTag },

    #[error(
        "pointer {ptr_tag} escapes allocation {alloc_tag} (offset {offset}, size {alloc_size})"
    )]
    OutOfBounds { ptr_tag: ProvenanceTag, alloc_tag: ProvenanceTag, offset: u64, alloc_size: u64 },

    #[error(
        "provenance mismatch: pointer has tag {ptr_tag} but dereferences into allocation {alloc_tag}"
    )]
    ProvenanceMismatch { ptr_tag: ProvenanceTag, alloc_tag: ProvenanceTag },

    #[error(
        "borrow stack violation: tag {tag} not found on stack for allocation {alloc_tag} (operation: {operation})"
    )]
    BorrowStackViolation { tag: ProvenanceTag, alloc_tag: ProvenanceTag, operation: String },

    #[error(
        "invalid reborrow: cannot create {new_perm} from {existing_perm} for allocation {alloc_tag}"
    )]
    InvalidReborrow { alloc_tag: ProvenanceTag, existing_perm: Permission, new_perm: Permission },
}

// ---------------------------------------------------------------------------
// ProvenanceTracker
// ---------------------------------------------------------------------------

/// Tracks provenance for all allocations and enforces Stacked Borrows.
///
/// This is the Layer 2 memory model: every pointer carries a `ProvenanceTag`
/// that identifies which allocation it was derived from. Operations on
/// pointers are checked against the borrow stack for that allocation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenanceTracker {
    /// All allocations, indexed by their provenance tag.
    allocations: BTreeMap<ProvenanceTag, AllocationInfo>,
    /// Map from region id to provenance tag (Layer 1 <-> Layer 2 bridge).
    region_to_tag: BTreeMap<RegionId, ProvenanceTag>,
    /// Next tag id to assign.
    next_tag: u64,
}

impl Default for ProvenanceTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl ProvenanceTracker {
    /// Create a new empty provenance tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            allocations: BTreeMap::new(),
            region_to_tag: BTreeMap::default(),
            next_tag: 1, // 0 reserved for null provenance
        }
    }

    /// Returns the number of live allocations.
    #[must_use]
    pub fn live_allocation_count(&self) -> usize {
        self.allocations.values().filter(|a| a.live).count()
    }

    /// Returns the total number of allocations (including freed).
    #[must_use]
    pub fn total_allocation_count(&self) -> usize {
        self.allocations.len()
    }

    // -----------------------------------------------------------------------
    // Allocation lifecycle
    // -----------------------------------------------------------------------

    /// Register a new allocation with the given size.
    ///
    /// Returns the `ProvenanceTag` assigned to this allocation.
    /// The borrow stack is initialized with a single `Unique` entry.
    pub fn allocate(&mut self, size: u64, region_id: Option<RegionId>) -> ProvenanceTag {
        let tag = self.fresh_tag();
        let info = AllocationInfo {
            tag,
            size,
            live: true,
            borrow_stack: vec![BorrowStackItem { tag, permission: Permission::Unique }],
            region_id,
        };
        self.allocations.insert(tag, info);
        if let Some(rid) = region_id {
            self.region_to_tag.insert(rid, tag);
        }
        tag
    }

    /// Free an allocation, marking it as no longer live.
    pub fn deallocate(&mut self, tag: ProvenanceTag) -> Result<(), ProvenanceError> {
        let info = self.allocations.get_mut(&tag).ok_or(ProvenanceError::UnknownTag { tag })?;
        if !info.live {
            return Err(ProvenanceError::DoubleFree { tag });
        }
        info.live = false;
        Ok(())
    }

    /// Look up allocation info by tag.
    pub fn get_allocation(&self, tag: ProvenanceTag) -> Result<&AllocationInfo, ProvenanceError> {
        self.allocations.get(&tag).ok_or(ProvenanceError::UnknownTag { tag })
    }

    /// Look up the provenance tag for a Layer 1 region.
    #[must_use]
    pub fn tag_for_region(&self, region_id: RegionId) -> Option<ProvenanceTag> {
        self.region_to_tag.get(&region_id).copied()
    }

    // -----------------------------------------------------------------------
    // Provenance checks
    // -----------------------------------------------------------------------

    /// Check that a pointer with the given tag can access the allocation
    /// at the given byte offset and access size.
    pub fn check_access(
        &self,
        ptr_tag: ProvenanceTag,
        offset: u64,
        access_size: u64,
    ) -> Result<(), ProvenanceError> {
        let info =
            self.allocations.get(&ptr_tag).ok_or(ProvenanceError::UnknownTag { tag: ptr_tag })?;

        if !info.live {
            return Err(ProvenanceError::UseAfterFree { tag: ptr_tag });
        }

        // Bounds check: offset + access_size must not exceed allocation size.
        // Allow one-past-the-end for zero-sized access.
        let end = offset.saturating_add(access_size);
        if end > info.size {
            return Err(ProvenanceError::OutOfBounds {
                ptr_tag,
                alloc_tag: info.tag,
                offset,
                alloc_size: info.size,
            });
        }

        Ok(())
    }

    /// Check that a pointer derived from `source_tag` can be used to access
    /// allocation `target_tag`. They must match.
    pub fn check_provenance_match(
        &self,
        ptr_tag: ProvenanceTag,
        alloc_tag: ProvenanceTag,
    ) -> Result<(), ProvenanceError> {
        if ptr_tag != alloc_tag {
            return Err(ProvenanceError::ProvenanceMismatch { ptr_tag, alloc_tag });
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Borrow stack operations (Stacked Borrows)
    // -----------------------------------------------------------------------

    /// Push a new borrow onto the stack for an allocation.
    ///
    /// This models creating a new reference (`&T`, `&mut T`, or raw pointer)
    /// to an allocation.
    pub fn push_borrow(
        &mut self,
        alloc_tag: ProvenanceTag,
        permission: Permission,
    ) -> Result<ProvenanceTag, ProvenanceError> {
        let new_tag = self.fresh_tag();

        let info = self
            .allocations
            .get_mut(&alloc_tag)
            .ok_or(ProvenanceError::UnknownTag { tag: alloc_tag })?;

        if !info.live {
            return Err(ProvenanceError::UseAfterFree { tag: alloc_tag });
        }

        // Validate the reborrow: check that the top of stack permits it.
        if let Some(top) = info.borrow_stack.last() {
            match (top.permission, permission) {
                // Unique can create anything.
                (Permission::Unique, _) => {}
                // SharedReadOnly can only create SharedReadOnly.
                (Permission::SharedReadOnly, Permission::SharedReadOnly) => {}
                (Permission::SharedReadOnly, new_perm) => {
                    return Err(ProvenanceError::InvalidReborrow {
                        alloc_tag,
                        existing_perm: top.permission,
                        new_perm,
                    });
                }
                // SharedReadWrite can create SharedReadOnly or SharedReadWrite.
                (Permission::SharedReadWrite, Permission::Unique) => {
                    return Err(ProvenanceError::InvalidReborrow {
                        alloc_tag,
                        existing_perm: top.permission,
                        new_perm: permission,
                    });
                }
                (Permission::SharedReadWrite, _) => {}
                // Disabled items should not be on top.
                (Permission::Disabled, _) => {
                    return Err(ProvenanceError::BorrowStackViolation {
                        tag: top.tag,
                        alloc_tag,
                        operation: "reborrow from disabled".into(),
                    });
                }
            }
        }

        info.borrow_stack.push(BorrowStackItem { tag: new_tag, permission });

        Ok(new_tag)
    }

    /// Use a tag for a read access, validating and potentially popping
    /// items from the borrow stack.
    ///
    /// For a read: find the tag on the stack. If found with read permission,
    /// the access is valid. No items are popped for shared reads.
    pub fn use_for_read(
        &mut self,
        alloc_tag: ProvenanceTag,
        use_tag: ProvenanceTag,
    ) -> Result<(), ProvenanceError> {
        let info = self
            .allocations
            .get_mut(&alloc_tag)
            .ok_or(ProvenanceError::UnknownTag { tag: alloc_tag })?;

        if !info.live {
            return Err(ProvenanceError::UseAfterFree { tag: alloc_tag });
        }

        // Find the tag on the stack.
        let found = info
            .borrow_stack
            .iter()
            .any(|item| item.tag == use_tag && item.permission != Permission::Disabled);

        if !found {
            return Err(ProvenanceError::BorrowStackViolation {
                tag: use_tag,
                alloc_tag,
                operation: "read".into(),
            });
        }

        Ok(())
    }

    /// Use a tag for a write access, popping all items above it on the stack.
    ///
    /// For a write: find the tag on the stack. If found with write permission
    /// (Unique or SharedReadWrite), pop/disable everything above it.
    pub fn use_for_write(
        &mut self,
        alloc_tag: ProvenanceTag,
        use_tag: ProvenanceTag,
    ) -> Result<(), ProvenanceError> {
        let info = self
            .allocations
            .get_mut(&alloc_tag)
            .ok_or(ProvenanceError::UnknownTag { tag: alloc_tag })?;

        if !info.live {
            return Err(ProvenanceError::UseAfterFree { tag: alloc_tag });
        }

        // Find the tag on the stack.
        let pos = info.borrow_stack.iter().position(|item| item.tag == use_tag);

        let pos = pos.ok_or(ProvenanceError::BorrowStackViolation {
            tag: use_tag,
            alloc_tag,
            operation: "write".into(),
        })?;

        let perm = info.borrow_stack[pos].permission;
        if perm == Permission::SharedReadOnly || perm == Permission::Disabled {
            return Err(ProvenanceError::BorrowStackViolation {
                tag: use_tag,
                alloc_tag,
                operation: format!("write (permission is {perm})"),
            });
        }

        // Disable all items above the found position.
        for item in &mut info.borrow_stack[(pos + 1)..] {
            item.permission = Permission::Disabled;
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // SMT encoding helpers
    // -----------------------------------------------------------------------

    /// Generate provenance-check verification conditions.
    ///
    /// Returns a list of formulas that must hold for provenance safety:
    /// - Each pointer access stays within its allocation bounds
    /// - No use-after-free
    #[must_use]
    pub fn generate_provenance_vcs(&self) -> Vec<ProvenanceVC> {
        let mut vcs = Vec::new();

        for info in self.allocations.values() {
            if !info.live {
                // For freed allocations, assert no further access.
                vcs.push(ProvenanceVC {
                    tag: info.tag,
                    kind: ProvenanceVCKind::NoUseAfterFree,
                    formula: Formula::Bool(true), // placeholder: solver checks reachability
                });
            }

            // For live allocations, encode bounds constraints.
            if info.live && info.size > 0 {
                let tag_name = format!("prov_{}", info.tag.0);
                let bounds = Formula::And(vec![
                    Formula::Ge(
                        Box::new(Formula::Var(
                            format!("{tag_name}_offset"),
                            trust_types::Sort::Int,
                        )),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Lt(
                        Box::new(Formula::Var(
                            format!("{tag_name}_offset"),
                            trust_types::Sort::Int,
                        )),
                        Box::new(Formula::Int(info.size as i128)),
                    ),
                ]);

                vcs.push(ProvenanceVC {
                    tag: info.tag,
                    kind: ProvenanceVCKind::InBounds,
                    formula: bounds,
                });
            }
        }

        vcs
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    fn fresh_tag(&mut self) -> ProvenanceTag {
        let tag = ProvenanceTag(self.next_tag);
        self.next_tag += 1;
        tag
    }
}

// ---------------------------------------------------------------------------
// Verification condition types
// ---------------------------------------------------------------------------

/// A provenance-related verification condition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenanceVC {
    /// The allocation this VC pertains to.
    pub tag: ProvenanceTag,
    /// What kind of provenance property this asserts.
    pub kind: ProvenanceVCKind,
    /// The SMT formula encoding the property.
    pub formula: Formula,
}

/// Kind of provenance verification condition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProvenanceVCKind {
    /// Pointer access is within allocation bounds.
    InBounds,
    /// No access to freed memory.
    NoUseAfterFree,
    /// Borrow stack is respected.
    BorrowStackValid,
}

impl std::fmt::Display for ProvenanceVCKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InBounds => write!(f, "in-bounds"),
            Self::NoUseAfterFree => write!(f, "no-use-after-free"),
            Self::BorrowStackValid => write!(f, "borrow-stack-valid"),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- Basic allocation ---

    #[test]
    fn test_allocate_returns_unique_tags() {
        let mut tracker = ProvenanceTracker::new();
        let t1 = tracker.allocate(16, None);
        let t2 = tracker.allocate(32, None);
        assert_ne!(t1, t2);
    }

    #[test]
    fn test_allocate_with_region_link() {
        let mut tracker = ProvenanceTracker::new();
        let region_id: RegionId = 42;
        let tag = tracker.allocate(8, Some(region_id));
        assert_eq!(tracker.tag_for_region(region_id), Some(tag));
    }

    #[test]
    fn test_allocation_info() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(64, None);
        let info = tracker.get_allocation(tag).expect("should exist");
        assert_eq!(info.tag(), tag);
        assert_eq!(info.size(), 64);
        assert!(info.is_live());
        assert_eq!(info.borrow_stack().len(), 1);
        assert_eq!(info.borrow_stack()[0].permission, Permission::Unique);
    }

    // --- Deallocation ---

    #[test]
    fn test_deallocate_marks_not_live() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(16, None);
        tracker.deallocate(tag).expect("dealloc ok");
        let info = tracker.get_allocation(tag).expect("still queryable");
        assert!(!info.is_live());
    }

    #[test]
    fn test_double_free_error() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(16, None);
        tracker.deallocate(tag).expect("first dealloc");
        let err = tracker.deallocate(tag).expect_err("double free");
        assert!(matches!(err, ProvenanceError::DoubleFree { .. }));
    }

    #[test]
    fn test_dealloc_unknown_tag_error() {
        let mut tracker = ProvenanceTracker::new();
        let err = tracker.deallocate(ProvenanceTag::from_raw(999)).expect_err("unknown");
        assert!(matches!(err, ProvenanceError::UnknownTag { .. }));
    }

    // --- Access checks ---

    #[test]
    fn test_check_access_valid() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(16, None);
        tracker.check_access(tag, 0, 8).expect("valid access");
        tracker.check_access(tag, 8, 8).expect("end of allocation");
    }

    #[test]
    fn test_check_access_out_of_bounds() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(16, None);
        let err = tracker.check_access(tag, 8, 16).expect_err("oob");
        assert!(matches!(err, ProvenanceError::OutOfBounds { .. }));
    }

    #[test]
    fn test_check_access_after_free() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(16, None);
        tracker.deallocate(tag).expect("dealloc");
        let err = tracker.check_access(tag, 0, 1).expect_err("use after free");
        assert!(matches!(err, ProvenanceError::UseAfterFree { .. }));
    }

    #[test]
    fn test_check_access_zero_size() {
        let mut tracker = ProvenanceTracker::new();
        let tag = tracker.allocate(16, None);
        // Zero-size access at end is valid (one-past-the-end).
        tracker.check_access(tag, 16, 0).expect("zero size at end");
    }

    // --- Provenance match ---

    #[test]
    fn test_provenance_match_same() {
        let tracker = ProvenanceTracker::new();
        let tag = ProvenanceTag::from_raw(5);
        tracker.check_provenance_match(tag, tag).expect("same tag matches");
    }

    #[test]
    fn test_provenance_mismatch() {
        let tracker = ProvenanceTracker::new();
        let t1 = ProvenanceTag::from_raw(1);
        let t2 = ProvenanceTag::from_raw(2);
        let err = tracker.check_provenance_match(t1, t2).expect_err("mismatch");
        assert!(matches!(err, ProvenanceError::ProvenanceMismatch { .. }));
    }

    // --- Borrow stack ---

    #[test]
    fn test_push_shared_borrow_from_unique() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let borrow_tag =
            tracker.push_borrow(alloc, Permission::SharedReadOnly).expect("shared from unique");
        assert_ne!(borrow_tag, alloc);

        let info = tracker.get_allocation(alloc).expect("exists");
        assert_eq!(info.borrow_stack().len(), 2);
    }

    #[test]
    fn test_push_mut_borrow_from_unique() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let borrow_tag =
            tracker.push_borrow(alloc, Permission::Unique).expect("unique from unique");
        assert_ne!(borrow_tag, alloc);
    }

    #[test]
    fn test_push_unique_from_shared_readonly_fails() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let _shared = tracker.push_borrow(alloc, Permission::SharedReadOnly).expect("shared");
        let err = tracker.push_borrow(alloc, Permission::Unique).expect_err("unique from shared");
        assert!(matches!(err, ProvenanceError::InvalidReborrow { .. }));
    }

    #[test]
    fn test_push_borrow_on_freed_fails() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        tracker.deallocate(alloc).expect("dealloc");
        let err = tracker.push_borrow(alloc, Permission::SharedReadOnly).expect_err("freed");
        assert!(matches!(err, ProvenanceError::UseAfterFree { .. }));
    }

    // --- Borrow stack read/write ---

    #[test]
    fn test_use_for_read_valid() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let shared = tracker.push_borrow(alloc, Permission::SharedReadOnly).expect("shared");
        tracker.use_for_read(alloc, shared).expect("read through shared");
        // Original tag also readable.
        tracker.use_for_read(alloc, alloc).expect("read through owner");
    }

    #[test]
    fn test_use_for_read_unknown_tag_fails() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let bogus = ProvenanceTag::from_raw(999);
        let err = tracker.use_for_read(alloc, bogus).expect_err("bogus tag");
        assert!(matches!(err, ProvenanceError::BorrowStackViolation { .. }));
    }

    #[test]
    fn test_use_for_write_pops_above() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let shared = tracker.push_borrow(alloc, Permission::SharedReadOnly).expect("shared");

        // Write through the original unique tag -- should disable shared.
        tracker.use_for_write(alloc, alloc).expect("write through owner");

        // Shared tag should now be disabled.
        let err = tracker.use_for_read(alloc, shared).expect_err("shared disabled");
        assert!(matches!(err, ProvenanceError::BorrowStackViolation { .. }));
    }

    #[test]
    fn test_use_for_write_through_shared_readonly_fails() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        let shared = tracker.push_borrow(alloc, Permission::SharedReadOnly).expect("shared");
        let err = tracker.use_for_write(alloc, shared).expect_err("write through readonly");
        assert!(matches!(err, ProvenanceError::BorrowStackViolation { .. }));
    }

    #[test]
    fn test_use_for_write_after_free_fails() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(8, None);
        tracker.deallocate(alloc).expect("dealloc");
        let err = tracker.use_for_write(alloc, alloc).expect_err("write after free");
        assert!(matches!(err, ProvenanceError::UseAfterFree { .. }));
    }

    // --- Counting ---

    #[test]
    fn test_live_and_total_counts() {
        let mut tracker = ProvenanceTracker::new();
        let t1 = tracker.allocate(8, None);
        let _t2 = tracker.allocate(16, None);
        assert_eq!(tracker.live_allocation_count(), 2);
        assert_eq!(tracker.total_allocation_count(), 2);

        tracker.deallocate(t1).expect("dealloc");
        assert_eq!(tracker.live_allocation_count(), 1);
        assert_eq!(tracker.total_allocation_count(), 2);
    }

    // --- Tag display ---

    #[test]
    fn test_provenance_tag_display() {
        let tag = ProvenanceTag::from_raw(42);
        assert_eq!(tag.to_string(), "prov#42");
    }

    // --- VC generation ---

    #[test]
    fn test_generate_provenance_vcs_live() {
        let mut tracker = ProvenanceTracker::new();
        let _t = tracker.allocate(32, None);
        let vcs = tracker.generate_provenance_vcs();
        assert!(!vcs.is_empty());
        assert!(vcs.iter().any(|vc| vc.kind == ProvenanceVCKind::InBounds));
    }

    #[test]
    fn test_generate_provenance_vcs_freed() {
        let mut tracker = ProvenanceTracker::new();
        let t = tracker.allocate(32, None);
        tracker.deallocate(t).expect("dealloc");
        let vcs = tracker.generate_provenance_vcs();
        assert!(vcs.iter().any(|vc| vc.kind == ProvenanceVCKind::NoUseAfterFree));
    }

    // --- Permission display ---

    #[test]
    fn test_permission_display() {
        assert_eq!(Permission::Unique.to_string(), "Unique");
        assert_eq!(Permission::SharedReadOnly.to_string(), "SharedReadOnly");
        assert_eq!(Permission::SharedReadWrite.to_string(), "SharedReadWrite");
        assert_eq!(Permission::Disabled.to_string(), "Disabled");
    }

    // --- ProvenanceVCKind display ---

    #[test]
    fn test_provenance_vc_kind_display() {
        assert_eq!(ProvenanceVCKind::InBounds.to_string(), "in-bounds");
        assert_eq!(ProvenanceVCKind::NoUseAfterFree.to_string(), "no-use-after-free");
        assert_eq!(ProvenanceVCKind::BorrowStackValid.to_string(), "borrow-stack-valid");
    }

    // --- Default ---

    #[test]
    fn test_tracker_default() {
        let tracker = ProvenanceTracker::default();
        assert_eq!(tracker.live_allocation_count(), 0);
        assert_eq!(tracker.total_allocation_count(), 0);
    }

    // --- Complex scenario: nested borrows ---

    #[test]
    fn test_nested_borrows_stacked() {
        let mut tracker = ProvenanceTracker::new();
        let alloc = tracker.allocate(64, None);

        // Create a chain: owner -> mut_borrow -> shared_borrow
        let mut_tag = tracker.push_borrow(alloc, Permission::Unique).expect("mut borrow");
        let shared_tag =
            tracker.push_borrow(alloc, Permission::SharedReadOnly).expect("shared from mut");

        // Read through all three.
        tracker.use_for_read(alloc, alloc).expect("read owner");
        tracker.use_for_read(alloc, mut_tag).expect("read mut");
        tracker.use_for_read(alloc, shared_tag).expect("read shared");

        // Write through mut -- disables shared above it.
        tracker.use_for_write(alloc, mut_tag).expect("write mut");

        // Shared is now disabled.
        let err = tracker.use_for_read(alloc, shared_tag).expect_err("shared disabled");
        assert!(matches!(err, ProvenanceError::BorrowStackViolation { .. }));

        // Mut and owner still work.
        tracker.use_for_read(alloc, mut_tag).expect("mut still ok");
        tracker.use_for_read(alloc, alloc).expect("owner still ok");
    }

    // --- ProvenanceTag roundtrip ---

    #[test]
    fn test_provenance_tag_raw_roundtrip() {
        let tag = ProvenanceTag::from_raw(123);
        assert_eq!(tag.as_raw(), 123);
    }
}
