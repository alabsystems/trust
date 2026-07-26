// trust-symex region-based memory model (Layer 1)
//
// Region-based encoding for safe Rust: each owned value occupies a unique
// region, shared refs are read-only aliases, mutable refs are exclusive.
// This is the simplest memory model layer -- sufficient for 90% of safe Rust.
//
// Design: Issue #146, VISION.md Section 9 (Memory Abstraction)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::{Formula, Sort, SortFromTy, Ty};

use crate::state::SymbolicValue;

// ---------------------------------------------------------------------------
// Region identifiers
// ---------------------------------------------------------------------------

/// Unique identifier for a memory region.
pub(crate) type RegionId = u64;

/// What kind of ownership a region represents.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OwnershipKind {
    /// Fully owned value (`let x = ...`).
    Owned,
    /// Shared (immutable) borrow (`&T`).
    SharedBorrow,
    /// Mutable (exclusive) borrow (`&mut T`).
    MutBorrow,
}

impl std::fmt::Display for OwnershipKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Owned => write!(f, "owned"),
            Self::SharedBorrow => write!(f, "&"),
            Self::MutBorrow => write!(f, "&mut"),
        }
    }
}

/// The state of a region in the region map.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RegionState {
    /// Region is live and accessible.
    Live,
    /// Region has been moved out -- source is invalidated.
    Moved,
    /// Region has been dropped.
    Dropped,
    /// Borrow has expired (scope ended).
    Expired,
}

impl std::fmt::Display for RegionState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Live => write!(f, "live"),
            Self::Moved => write!(f, "moved"),
            Self::Dropped => write!(f, "dropped"),
            Self::Expired => write!(f, "expired"),
        }
    }
}

// ---------------------------------------------------------------------------
// Region
// ---------------------------------------------------------------------------

/// A memory region in the region-based model.
///
/// Each owned value, shared borrow, or mutable borrow gets its own region.
/// Regions form a tree: an owner region may have child borrow regions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Region {
    /// Unique identifier.
    id: RegionId,
    /// Human-readable name (variable name or generated).
    name: String,
    /// The type stored in this region.
    ty: Ty,
    /// What kind of ownership this region represents.
    ownership: OwnershipKind,
    /// Current state (live, moved, dropped, expired).
    state: RegionState,
    /// The parent region this borrows from (None for owned regions).
    parent: Option<RegionId>,
    /// Child borrow regions.
    children: BTreeSet<RegionId>,
    /// Scope depth at which this region was created.
    scope_depth: u32,
}

impl Region {
    /// Returns the region's unique id.
    #[must_use]
    pub fn id(&self) -> RegionId {
        self.id
    }

    /// Returns the region's name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the type stored in this region.
    #[must_use]
    pub fn ty(&self) -> &Ty {
        &self.ty
    }

    /// Returns the ownership kind.
    #[must_use]
    pub fn ownership(&self) -> OwnershipKind {
        self.ownership
    }

    /// Returns the current state.
    #[must_use]
    pub fn state(&self) -> RegionState {
        self.state
    }

    /// Returns the parent region id, if any.
    #[must_use]
    pub fn parent(&self) -> Option<RegionId> {
        self.parent
    }

    /// Returns the scope depth at creation.
    #[must_use]
    pub fn scope_depth(&self) -> u32 {
        self.scope_depth
    }

    /// Returns true if the region is in a live state.
    #[must_use]
    pub fn is_live(&self) -> bool {
        self.state == RegionState::Live
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from region-based memory operations.
#[derive(Debug, Clone, Error, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RegionError {
    #[error("region {id} not found (name: {name})")]
    RegionNotFound { id: RegionId, name: String },

    #[error("use after move: region `{name}` (id {id}) was moved")]
    UseAfterMove { id: RegionId, name: String },

    #[error("use after drop: region `{name}` (id {id}) was dropped")]
    UseAfterDrop { id: RegionId, name: String },

    #[error("expired borrow: region `{name}` (id {id}) borrow has expired")]
    ExpiredBorrow { id: RegionId, name: String },

    #[error("write to shared borrow: region `{name}` (id {id}) is read-only")]
    WriteToSharedBorrow { id: RegionId, name: String },

    #[error("exclusivity violation: region `{name}` (id {id}) has active borrows")]
    ExclusivityViolation { id: RegionId, name: String, active_borrows: Vec<RegionId> },

    #[error(
        "borrow outlives owner: borrow `{borrow_name}` (scope {borrow_scope}) outlives owner `{owner_name}` (scope {owner_scope})"
    )]
    BorrowOutlivesOwner {
        borrow_name: String,
        borrow_scope: u32,
        owner_name: String,
        owner_scope: u32,
    },

    #[error("double move: region `{name}` (id {id}) was already moved")]
    DoubleMove { id: RegionId, name: String },

    #[error("double drop: region `{name}` (id {id}) was already dropped")]
    DoubleDrop { id: RegionId, name: String },

    #[error("cannot borrow moved region `{name}` (id {id})")]
    BorrowOfMoved { id: RegionId, name: String },

    #[error(
        "cannot create mutable borrow: region `{name}` (id {id}) already has active shared borrows"
    )]
    MutBorrowWithSharedActive { id: RegionId, name: String, shared_borrows: Vec<RegionId> },

    #[error(
        "cannot create shared borrow: region `{name}` (id {id}) already has an active mutable borrow"
    )]
    SharedBorrowWithMutActive { id: RegionId, name: String, mut_borrow: RegionId },

    #[error("array index out of bounds: index {index} >= length {length} in region `{name}`")]
    ArrayIndexOutOfBounds { name: String, index: u64, length: u64 },

    #[error("field `{field}` not found in struct region `{name}`")]
    FieldNotFound { name: String, field: String },
}

// ---------------------------------------------------------------------------
// RegionMap
// ---------------------------------------------------------------------------

/// Tracks all memory regions and their relationships.
///
/// This is the core data structure for the region-based memory model.
/// It maps variable names to region ids, tracks the region tree
/// (owner -> borrows), and stores symbolic values per region.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegionMap {
    /// All regions, indexed by id.
    regions: BTreeMap<RegionId, Region>,
    /// Map from variable name to region id.
    name_to_region: BTreeMap<String, RegionId>,
    /// Symbolic values stored in each region.
    values: BTreeMap<RegionId, SymbolicValue>,
    /// Struct field sub-regions: (parent_region, field_name) -> field_region.
    field_regions: BTreeMap<(RegionId, String), RegionId>,
    /// Array element regions: (parent_region, index) -> element_region.
    array_element_regions: BTreeMap<(RegionId, u64), RegionId>,
    /// Next region id to assign.
    next_id: RegionId,
    /// Current scope depth.
    current_scope: u32,
}

impl Default for RegionMap {
    fn default() -> Self {
        Self::new()
    }
}

impl RegionMap {
    /// Create a new empty region map.
    #[must_use]
    pub fn new() -> Self {
        Self {
            regions: BTreeMap::new(),
            name_to_region: BTreeMap::default(),
            values: BTreeMap::default(),
            field_regions: BTreeMap::default(),
            array_element_regions: BTreeMap::default(),
            next_id: 0,
            current_scope: 0,
        }
    }

    /// Returns the current scope depth.
    #[must_use]
    pub fn current_scope(&self) -> u32 {
        self.current_scope
    }

    /// Enter a new scope (e.g., entering a block).
    pub fn enter_scope(&mut self) {
        self.current_scope += 1;
    }

    /// Exit the current scope, expiring all borrows created at this depth.
    ///
    /// Returns the list of expired region ids.
    pub fn exit_scope(&mut self) -> Vec<RegionId> {
        let mut expired = Vec::new();
        let current = self.current_scope;

        // Collect regions to expire (borrows at current scope depth).
        let to_expire: Vec<RegionId> = self
            .regions
            .values()
            .filter(|r| {
                r.scope_depth == current
                    && r.state == RegionState::Live
                    && matches!(r.ownership, OwnershipKind::SharedBorrow | OwnershipKind::MutBorrow)
            })
            .map(|r| r.id)
            .collect();

        for id in to_expire {
            if let Some(region) = self.regions.get_mut(&id) {
                region.state = RegionState::Expired;
                expired.push(id);

                // Remove from parent's children.
                if let Some(parent_id) = region.parent
                    && let Some(parent) = self.regions.get_mut(&parent_id)
                {
                    parent.children.remove(&id);
                }
            }
        }

        self.current_scope = current.saturating_sub(1);
        expired
    }

    /// Returns the number of live regions.
    #[must_use]
    pub fn live_region_count(&self) -> usize {
        self.regions.values().filter(|r| r.state == RegionState::Live).count()
    }

    /// Returns the total number of regions (including dead ones).
    #[must_use]
    pub fn total_region_count(&self) -> usize {
        self.regions.len()
    }

    // -----------------------------------------------------------------------
    // Region creation
    // -----------------------------------------------------------------------

    /// Create a new owned region for a variable binding (`let x: T = ...`).
    pub fn bind_owned(
        &mut self,
        name: impl Into<String>,
        ty: Ty,
        value: SymbolicValue,
    ) -> RegionId {
        let name = name.into();
        let id = self.alloc_id();
        let region = Region {
            id,
            name: name.clone(),
            ty,
            ownership: OwnershipKind::Owned,
            state: RegionState::Live,
            parent: None,
            children: BTreeSet::new(),
            scope_depth: self.current_scope,
        };
        self.regions.insert(id, region);
        self.name_to_region.insert(name, id);
        self.values.insert(id, value);
        id
    }

    /// Create a new owned region for a function parameter.
    pub fn bind_param(&mut self, name: impl Into<String>, ty: Ty) -> RegionId {
        let name_str: String = name.into();
        let sym = SymbolicValue::Symbol(name_str.clone());
        self.bind_owned(name_str, ty, sym)
    }

    /// Create a shared borrow (`&T`) of an existing region.
    pub fn borrow_shared(
        &mut self,
        borrow_name: impl Into<String>,
        owner_id: RegionId,
    ) -> Result<RegionId, RegionError> {
        let owner = self.get_region(owner_id)?;
        self.check_live(owner)?;

        // Cannot create a shared borrow if there's an active mutable borrow.
        let active_mut = self.active_mut_borrows(owner_id);
        if let Some(&mut_id) = active_mut.first() {
            let owner = self.get_region(owner_id)?;
            return Err(RegionError::SharedBorrowWithMutActive {
                id: owner_id,
                name: owner.name.clone(),
                mut_borrow: mut_id,
            });
        }

        let owner = self.get_region(owner_id)?;
        let borrow_name = borrow_name.into();
        let inner_ty = owner.ty.clone();
        let borrow_ty = Ty::Ref { mutable: false, inner: Box::new(inner_ty) };

        let id = self.alloc_id();
        let region = Region {
            id,
            name: borrow_name.clone(),
            ty: borrow_ty,
            ownership: OwnershipKind::SharedBorrow,
            state: RegionState::Live,
            parent: Some(owner_id),
            children: BTreeSet::new(),
            scope_depth: self.current_scope,
        };
        self.regions.insert(id, region);
        self.name_to_region.insert(borrow_name, id);

        // Shared borrow reads the same value as the owner.
        if let Some(val) = self.values.get(&owner_id).cloned() {
            self.values.insert(id, val);
        }

        // Register as child of owner.
        if let Some(owner_region) = self.regions.get_mut(&owner_id) {
            owner_region.children.insert(id);
        }

        Ok(id)
    }

    /// Create a mutable borrow (`&mut T`) of an existing region.
    pub fn borrow_mut(
        &mut self,
        borrow_name: impl Into<String>,
        owner_id: RegionId,
    ) -> Result<RegionId, RegionError> {
        let owner = self.get_region(owner_id)?;
        self.check_live(owner)?;

        // Cannot create mutable borrow if there are any active borrows.
        let active_shared = self.active_shared_borrows(owner_id);
        if !active_shared.is_empty() {
            let owner = self.get_region(owner_id)?;
            return Err(RegionError::MutBorrowWithSharedActive {
                id: owner_id,
                name: owner.name.clone(),
                shared_borrows: active_shared,
            });
        }

        let active_mut = self.active_mut_borrows(owner_id);
        if !active_mut.is_empty() {
            let owner = self.get_region(owner_id)?;
            return Err(RegionError::ExclusivityViolation {
                id: owner_id,
                name: owner.name.clone(),
                active_borrows: active_mut,
            });
        }

        let owner = self.get_region(owner_id)?;
        let borrow_name = borrow_name.into();
        let inner_ty = owner.ty.clone();
        let borrow_ty = Ty::Ref { mutable: true, inner: Box::new(inner_ty) };

        let id = self.alloc_id();
        let region = Region {
            id,
            name: borrow_name.clone(),
            ty: borrow_ty,
            ownership: OwnershipKind::MutBorrow,
            state: RegionState::Live,
            parent: Some(owner_id),
            children: BTreeSet::new(),
            scope_depth: self.current_scope,
        };
        self.regions.insert(id, region);
        self.name_to_region.insert(borrow_name, id);

        // Mutable borrow reads the current value.
        if let Some(val) = self.values.get(&owner_id).cloned() {
            self.values.insert(id, val);
        }

        // Register as child of owner.
        if let Some(owner_region) = self.regions.get_mut(&owner_id) {
            owner_region.children.insert(id);
        }

        Ok(id)
    }

    // -----------------------------------------------------------------------
    // Struct field decomposition
    // -----------------------------------------------------------------------

    /// Access a struct field, creating a sub-region if needed.
    ///
    /// Per the design: `p.x` -> separate variable `p_x`.
    pub fn field_access(
        &mut self,
        parent_id: RegionId,
        field_name: &str,
    ) -> Result<RegionId, RegionError> {
        let parent = self.get_region(parent_id)?;
        self.check_accessible(parent)?;

        // Check if we already have a sub-region for this field.
        let key = (parent_id, field_name.to_owned());
        if let Some(&existing) = self.field_regions.get(&key) {
            return Ok(existing);
        }

        // Look up the field type.
        let parent = self.get_region(parent_id)?;
        let field_ty = match &parent.ty {
            Ty::Adt { fields, .. } => {
                fields.iter().find(|(name, _)| name == field_name).map(|(_, ty)| ty.clone())
            }
            _ => None,
        };

        let field_ty = field_ty.ok_or_else(|| RegionError::FieldNotFound {
            name: parent.name.clone(),
            field: field_name.to_owned(),
        })?;

        let parent = self.get_region(parent_id)?;
        let parent_name = parent.name.clone();
        let parent_ownership = parent.ownership;
        let sub_name = format!("{}_{}", parent_name, field_name);

        let id = self.alloc_id();
        let region = Region {
            id,
            name: sub_name.clone(),
            ty: field_ty,
            ownership: parent_ownership,
            state: RegionState::Live,
            parent: Some(parent_id),
            children: BTreeSet::new(),
            scope_depth: self.current_scope,
        };
        self.regions.insert(id, region);
        self.name_to_region.insert(sub_name.clone(), id);

        // Create a symbolic value for the field.
        let sym = SymbolicValue::Symbol(sub_name);
        self.values.insert(id, sym);

        self.field_regions.insert(key, id);
        if let Some(parent_region) = self.regions.get_mut(&parent_id) {
            parent_region.children.insert(id);
        }

        Ok(id)
    }

    // -----------------------------------------------------------------------
    // Array access
    // -----------------------------------------------------------------------

    /// Access an array element at a concrete index.
    ///
    /// Per the design: `arr[i]` -> bounds check + select.
    /// For concrete indices, creates a sub-region for the element.
    pub fn array_access(
        &mut self,
        parent_id: RegionId,
        index: u64,
    ) -> Result<RegionId, RegionError> {
        let parent = self.get_region(parent_id)?;
        self.check_accessible(parent)?;

        // Bounds check.
        let parent = self.get_region(parent_id)?;
        if let Ty::Array { len, .. } = &parent.ty
            && index >= *len
        {
            return Err(RegionError::ArrayIndexOutOfBounds {
                name: parent.name.clone(),
                index,
                length: *len,
            });
        }

        // Check if we already have a sub-region for this index.
        let key = (parent_id, index);
        if let Some(&existing) = self.array_element_regions.get(&key) {
            return Ok(existing);
        }

        // Look up element type.
        let parent = self.get_region(parent_id)?;
        let elem_ty = match &parent.ty {
            Ty::Array { elem, .. } | Ty::Slice { elem } => (**elem).clone(),
            _ => {
                return Err(RegionError::FieldNotFound {
                    name: parent.name.clone(),
                    field: format!("[{index}]"),
                });
            }
        };

        let parent = self.get_region(parent_id)?;
        let parent_name = parent.name.clone();
        let parent_ownership = parent.ownership;
        let elem_name = format!("{}_elem_{}", parent_name, index);

        let id = self.alloc_id();
        let region = Region {
            id,
            name: elem_name.clone(),
            ty: elem_ty,
            ownership: parent_ownership,
            state: RegionState::Live,
            parent: Some(parent_id),
            children: BTreeSet::new(),
            scope_depth: self.current_scope,
        };
        self.regions.insert(id, region);
        self.name_to_region.insert(elem_name.clone(), id);

        let sym = SymbolicValue::Symbol(elem_name);
        self.values.insert(id, sym);

        self.array_element_regions.insert(key, id);
        if let Some(parent_region) = self.regions.get_mut(&parent_id) {
            parent_region.children.insert(id);
        }

        Ok(id)
    }

    // -----------------------------------------------------------------------
    // Read / Write
    // -----------------------------------------------------------------------

    /// Read the symbolic value from a region.
    pub fn read(&self, id: RegionId) -> Result<&SymbolicValue, RegionError> {
        let region = self.get_region(id)?;
        self.check_accessible(region)?;

        self.values.get(&id).ok_or_else(|| {
            let region = self
                .regions
                .get(&id)
                // SAFETY: get_region(id)? succeeded above, so regions contains this id.
                .expect("invariant: get_region(id) succeeded, so regions must contain this id");
            RegionError::RegionNotFound { id, name: region.name.clone() }
        })
    }

    /// Write a symbolic value to a region.
    ///
    /// Enforces: cannot write to shared borrows, cannot write to non-live regions.
    pub fn write(&mut self, id: RegionId, value: SymbolicValue) -> Result<(), RegionError> {
        let region = self.get_region(id)?;
        self.check_accessible(region)?;

        // Shared borrows are read-only.
        if region.ownership == OwnershipKind::SharedBorrow {
            return Err(RegionError::WriteToSharedBorrow { id, name: region.name.clone() });
        }

        // Check no active borrows exist when writing through owner.
        if region.ownership == OwnershipKind::Owned {
            let active: Vec<RegionId> = region
                .children
                .iter()
                .filter(|child_id| {
                    self.regions.get(child_id).is_some_and(|r| r.state == RegionState::Live)
                })
                .copied()
                .collect();
            if !active.is_empty() {
                return Err(RegionError::ExclusivityViolation {
                    id,
                    name: region.name.clone(),
                    active_borrows: active,
                });
            }
        }

        self.values.insert(id, value);
        Ok(())
    }

    /// Write through a mutable borrow, propagating the value to the owner.
    pub fn write_through_mut_borrow(
        &mut self,
        borrow_id: RegionId,
        value: SymbolicValue,
    ) -> Result<(), RegionError> {
        let region = self.get_region(borrow_id)?;
        self.check_accessible(region)?;

        if region.ownership != OwnershipKind::MutBorrow {
            return Err(RegionError::WriteToSharedBorrow {
                id: borrow_id,
                name: region.name.clone(),
            });
        }

        let parent_id = region.parent;
        self.values.insert(borrow_id, value.clone());

        // Propagate write to the owner region.
        if let Some(pid) = parent_id {
            self.values.insert(pid, value);
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Move semantics
    // -----------------------------------------------------------------------

    /// Move a value from one region to a new region, invalidating the source.
    pub fn move_value(
        &mut self,
        source_id: RegionId,
        dest_name: impl Into<String>,
    ) -> Result<RegionId, RegionError> {
        let source = self.get_region(source_id)?;
        self.check_accessible(source)?;

        // Cannot move if there are active borrows.
        let active: Vec<RegionId> = source
            .children
            .iter()
            .filter(|child_id| {
                self.regions.get(child_id).is_some_and(|r| r.state == RegionState::Live)
            })
            .copied()
            .collect();
        if !active.is_empty() {
            return Err(RegionError::ExclusivityViolation {
                id: source_id,
                name: source.name.clone(),
                active_borrows: active,
            });
        }

        let source = self.get_region(source_id)?;
        let ty = source.ty.clone();
        let value = self
            .values
            .get(&source_id)
            .cloned()
            .unwrap_or_else(|| SymbolicValue::Symbol(format!("moved_from_{}", source.name)));

        // Invalidate source.
        if let Some(s) = self.regions.get_mut(&source_id) {
            s.state = RegionState::Moved;
        }

        // Create destination region.
        let dest_name = dest_name.into();
        let dest_id = self.bind_owned(dest_name, ty, value);
        Ok(dest_id)
    }

    // -----------------------------------------------------------------------
    // Drop tracking
    // -----------------------------------------------------------------------

    /// Mark a region as dropped.
    pub fn drop_region(&mut self, id: RegionId) -> Result<(), RegionError> {
        let region = self.get_region(id)?;
        match region.state {
            RegionState::Live => {}
            RegionState::Moved => {
                // Dropping a moved region is a no-op (already moved out).
                return Ok(());
            }
            RegionState::Dropped => {
                return Err(RegionError::DoubleDrop { id, name: region.name.clone() });
            }
            RegionState::Expired => {
                // Expired borrows are already cleaned up.
                return Ok(());
            }
        }

        // Expire all child borrows first.
        let children: Vec<RegionId> = region.children.iter().copied().collect();
        for child_id in children {
            if let Some(child) = self.regions.get_mut(&child_id)
                && child.state == RegionState::Live
            {
                child.state = RegionState::Expired;
            }
        }

        if let Some(r) = self.regions.get_mut(&id) {
            r.state = RegionState::Dropped;
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Lookup helpers
    // -----------------------------------------------------------------------

    /// Look up a region by name.
    pub fn lookup_by_name(&self, name: &str) -> Result<RegionId, RegionError> {
        self.name_to_region
            .get(name)
            .copied()
            .ok_or_else(|| RegionError::RegionNotFound { id: 0, name: name.to_owned() })
    }

    /// Get a region by id (immutable).
    pub fn get_region(&self, id: RegionId) -> Result<&Region, RegionError> {
        self.regions
            .get(&id)
            .ok_or_else(|| RegionError::RegionNotFound { id, name: format!("<unknown:{id}>") })
    }

    /// Iterate over all live regions.
    pub fn live_regions(&self) -> impl Iterator<Item = &Region> {
        self.regions.values().filter(|r| r.state == RegionState::Live)
    }

    /// Iterate over all regions.
    pub fn all_regions(&self) -> impl Iterator<Item = &Region> {
        self.regions.values()
    }

    /// Get all active shared borrows of a region.
    #[must_use]
    pub fn active_shared_borrows(&self, owner_id: RegionId) -> Vec<RegionId> {
        self.regions
            .get(&owner_id)
            .map(|r| {
                r.children
                    .iter()
                    .filter(|child_id| {
                        self.regions.get(child_id).is_some_and(|child| {
                            child.state == RegionState::Live
                                && child.ownership == OwnershipKind::SharedBorrow
                        })
                    })
                    .copied()
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get all active mutable borrows of a region.
    #[must_use]
    pub fn active_mut_borrows(&self, owner_id: RegionId) -> Vec<RegionId> {
        self.regions
            .get(&owner_id)
            .map(|r| {
                r.children
                    .iter()
                    .filter(|child_id| {
                        self.regions.get(child_id).is_some_and(|child| {
                            child.state == RegionState::Live
                                && child.ownership == OwnershipKind::MutBorrow
                        })
                    })
                    .copied()
                    .collect()
            })
            .unwrap_or_default()
    }

    // -----------------------------------------------------------------------
    // SMT encoding helpers
    // -----------------------------------------------------------------------

    /// Generate an SMT variable name for a region.
    ///
    /// Per the design: each MIR Place maps to a separate SMT symbol.
    #[must_use]
    pub fn smt_var_name(&self, id: RegionId) -> Option<String> {
        self.regions.get(&id).map(|r| {
            // Sanitize name for SMT (replace dots, brackets).
            r.name.replace(['.', '['], "_").replace(']', "")
        })
    }

    /// Generate the SMT sort for a region's type.
    #[must_use]
    pub fn smt_sort(&self, id: RegionId) -> Option<Sort> {
        self.regions.get(&id).map(|r| Sort::from_ty(&r.ty))
    }

    /// Generate a Formula::Var for a region.
    #[must_use]
    pub fn to_formula_var(&self, id: RegionId) -> Option<Formula> {
        let name = self.smt_var_name(id)?;
        let sort = self.smt_sort(id)?;
        Some(Formula::Var(name, sort))
    }

    /// Generate an array bounds-check formula for an array access.
    ///
    /// Returns a formula that is satisfiable when the index is OUT of bounds
    /// (i.e., the violation formula).
    #[must_use]
    pub fn array_bounds_check_formula(
        &self,
        array_id: RegionId,
        index_formula: &Formula,
    ) -> Option<Formula> {
        let region = self.regions.get(&array_id)?;
        let length = match &region.ty {
            Ty::Array { len, .. } => *len,
            _ => return None,
        };

        // Violation: index < 0 OR index >= length
        let zero = Formula::Int(0);
        let len_formula = Formula::Int(length as i128);

        Some(Formula::Or(vec![
            Formula::Lt(Box::new(index_formula.clone()), Box::new(zero)),
            Formula::Ge(Box::new(index_formula.clone()), Box::new(len_formula)),
        ]))
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    fn alloc_id(&mut self) -> RegionId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn check_live(&self, region: &Region) -> Result<(), RegionError> {
        match region.state {
            RegionState::Live => Ok(()),
            RegionState::Moved => {
                Err(RegionError::BorrowOfMoved { id: region.id, name: region.name.clone() })
            }
            RegionState::Dropped => {
                Err(RegionError::UseAfterDrop { id: region.id, name: region.name.clone() })
            }
            RegionState::Expired => {
                Err(RegionError::ExpiredBorrow { id: region.id, name: region.name.clone() })
            }
        }
    }

    fn check_accessible(&self, region: &Region) -> Result<(), RegionError> {
        match region.state {
            RegionState::Live => Ok(()),
            RegionState::Moved => {
                Err(RegionError::UseAfterMove { id: region.id, name: region.name.clone() })
            }
            RegionState::Dropped => {
                Err(RegionError::UseAfterDrop { id: region.id, name: region.name.clone() })
            }
            RegionState::Expired => {
                Err(RegionError::ExpiredBorrow { id: region.id, name: region.name.clone() })
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::Ty;

    fn i32_ty() -> Ty {
        Ty::i32()
    }

    fn u64_ty() -> Ty {
        Ty::Int { width: 64, signed: false }
    }

    fn array_i32_ty(len: u64) -> Ty {
        Ty::Array { elem: Box::new(i32_ty()), len }
    }

    fn struct_point_ty() -> Ty {
        Ty::Adt { adt_kind: None, layout: None, variants: Vec::new(),
            name: "Point".into(),
            fields: vec![("x".into(), i32_ty()), ("y".into(), i32_ty())],
            disc_index_safe: false,
         faithful_enum_repr: None, enum_layout: None, }
    }

    // --- Basic binding and read ---

    #[test]
    fn test_bind_owned_and_read() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(42));
        let val = map.read(id).expect("should read");
        assert_eq!(*val, SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_bind_param() {
        let mut map = RegionMap::new();
        let id = map.bind_param("n", i32_ty());
        let val = map.read(id).expect("should read");
        assert_eq!(*val, SymbolicValue::Symbol("n".into()));
    }

    #[test]
    fn test_lookup_by_name() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        assert_eq!(map.lookup_by_name("x").expect("found"), id);
        assert!(map.lookup_by_name("y").is_err());
    }

    // --- Write ---

    #[test]
    fn test_write_to_owned() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        map.write(id, SymbolicValue::Concrete(2)).expect("write ok");
        let val = map.read(id).expect("read");
        assert_eq!(*val, SymbolicValue::Concrete(2));
    }

    #[test]
    fn test_write_to_shared_borrow_fails() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let borrow = map.borrow_shared("ref_x", owner).expect("borrow");
        let err = map.write(borrow, SymbolicValue::Concrete(2)).expect_err("should fail");
        assert!(matches!(err, RegionError::WriteToSharedBorrow { .. }));
    }

    // --- Shared borrows ---

    #[test]
    fn test_shared_borrow_reads_owner_value() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(10));
        let borrow = map.borrow_shared("ref_x", owner).expect("borrow");
        let val = map.read(borrow).expect("read borrow");
        assert_eq!(*val, SymbolicValue::Concrete(10));
    }

    #[test]
    fn test_multiple_shared_borrows_allowed() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(5));
        let b1 = map.borrow_shared("r1", owner).expect("borrow 1");
        let b2 = map.borrow_shared("r2", owner).expect("borrow 2");
        assert_ne!(b1, b2);
        assert_eq!(*map.read(b1).expect("read b1"), SymbolicValue::Concrete(5));
        assert_eq!(*map.read(b2).expect("read b2"), SymbolicValue::Concrete(5));
    }

    // --- Mutable borrows ---

    #[test]
    fn test_mut_borrow_is_exclusive() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _mb = map.borrow_mut("mut_x", owner).expect("mut borrow");
        let err = map.borrow_mut("mut_x2", owner).expect_err("second mut");
        assert!(matches!(err, RegionError::ExclusivityViolation { .. }));
    }

    #[test]
    fn test_mut_borrow_blocks_shared() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _mb = map.borrow_mut("mut_x", owner).expect("mut borrow");
        let err = map.borrow_shared("ref_x", owner).expect_err("shared after mut");
        assert!(matches!(err, RegionError::SharedBorrowWithMutActive { .. }));
    }

    #[test]
    fn test_shared_borrow_blocks_mut() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _sb = map.borrow_shared("ref_x", owner).expect("shared borrow");
        let err = map.borrow_mut("mut_x", owner).expect_err("mut after shared");
        assert!(matches!(err, RegionError::MutBorrowWithSharedActive { .. }));
    }

    #[test]
    fn test_write_through_mut_borrow() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let mb = map.borrow_mut("mut_x", owner).expect("mut borrow");
        map.write_through_mut_borrow(mb, SymbolicValue::Concrete(99)).expect("write through");
        // Both borrow and owner should reflect the new value.
        assert_eq!(*map.read(mb).expect("read borrow"), SymbolicValue::Concrete(99));
        // Owner value also updated.
        assert_eq!(*map.values.get(&owner).expect("owner value"), SymbolicValue::Concrete(99));
    }

    // --- Scope-based lifetime tracking ---

    #[test]
    fn test_borrow_expires_on_scope_exit() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));

        map.enter_scope();
        let borrow = map.borrow_shared("ref_x", owner).expect("borrow");
        assert!(map.read(borrow).is_ok());

        let expired = map.exit_scope();
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0], borrow);

        // Borrow is now expired.
        let err = map.read(borrow).expect_err("should be expired");
        assert!(matches!(err, RegionError::ExpiredBorrow { .. }));
    }

    #[test]
    fn test_nested_scopes() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));

        map.enter_scope(); // depth 1
        let b1 = map.borrow_shared("r1", owner).expect("borrow 1");

        map.enter_scope(); // depth 2
        let b2 = map.borrow_shared("r2", owner).expect("borrow 2");

        // Exit inner scope -- only b2 expires.
        let expired = map.exit_scope();
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0], b2);

        // b1 still alive.
        assert!(map.read(b1).is_ok());

        // Exit outer scope -- b1 expires.
        let expired = map.exit_scope();
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0], b1);
    }

    #[test]
    fn test_mut_borrow_after_scope_exit() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));

        map.enter_scope();
        let _sb = map.borrow_shared("ref_x", owner).expect("shared borrow");
        map.exit_scope();

        // Now mut borrow should succeed since shared borrow expired.
        let mb = map.borrow_mut("mut_x", owner).expect("mut borrow after expire");
        assert!(map.read(mb).is_ok());
    }

    // --- Move semantics ---

    #[test]
    fn test_move_invalidates_source() {
        let mut map = RegionMap::new();
        let src = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(42));
        let dest = map.move_value(src, "y").expect("move ok");

        // Destination has the value.
        assert_eq!(*map.read(dest).expect("read dest"), SymbolicValue::Concrete(42));

        // Source is invalidated.
        let err = map.read(src).expect_err("source should be moved");
        assert!(matches!(err, RegionError::UseAfterMove { .. }));
    }

    #[test]
    fn test_move_with_active_borrow_fails() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _borrow = map.borrow_shared("ref_x", owner).expect("borrow");
        let err = map.move_value(owner, "y").expect_err("move with borrow");
        assert!(matches!(err, RegionError::ExclusivityViolation { .. }));
    }

    #[test]
    fn test_double_move_fails() {
        let mut map = RegionMap::new();
        let src = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _dest = map.move_value(src, "y").expect("first move");
        let err = map.move_value(src, "z").expect_err("second move");
        assert!(matches!(err, RegionError::UseAfterMove { .. }));
    }

    // --- Drop tracking ---

    #[test]
    fn test_drop_marks_region_dropped() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        map.drop_region(id).expect("drop ok");
        let err = map.read(id).expect_err("use after drop");
        assert!(matches!(err, RegionError::UseAfterDrop { .. }));
    }

    #[test]
    fn test_double_drop_fails() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        map.drop_region(id).expect("first drop");
        let err = map.drop_region(id).expect_err("double drop");
        assert!(matches!(err, RegionError::DoubleDrop { .. }));
    }

    #[test]
    fn test_drop_expires_child_borrows() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let borrow = map.borrow_shared("ref_x", owner).expect("borrow");
        map.drop_region(owner).expect("drop owner");
        let err = map.read(borrow).expect_err("borrow expired");
        assert!(matches!(err, RegionError::ExpiredBorrow { .. }));
    }

    #[test]
    fn test_drop_moved_is_noop() {
        let mut map = RegionMap::new();
        let src = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _dest = map.move_value(src, "y").expect("move");
        // Dropping a moved value is fine (no-op).
        map.drop_region(src).expect("drop moved is noop");
    }

    // --- Struct field access ---

    #[test]
    fn test_struct_field_access() {
        let mut map = RegionMap::new();
        let pt = map.bind_owned("p", struct_point_ty(), SymbolicValue::Symbol("p".into()));
        let x_id = map.field_access(pt, "x").expect("field x");
        let y_id = map.field_access(pt, "y").expect("field y");
        assert_ne!(x_id, y_id);

        // Field values are symbolic.
        let x_val = map.read(x_id).expect("read x");
        assert_eq!(*x_val, SymbolicValue::Symbol("p_x".into()));

        let y_val = map.read(y_id).expect("read y");
        assert_eq!(*y_val, SymbolicValue::Symbol("p_y".into()));
    }

    #[test]
    fn test_struct_field_access_idempotent() {
        let mut map = RegionMap::new();
        let pt = map.bind_owned("p", struct_point_ty(), SymbolicValue::Symbol("p".into()));
        let x1 = map.field_access(pt, "x").expect("first access");
        let x2 = map.field_access(pt, "x").expect("second access");
        assert_eq!(x1, x2, "repeated field access returns same region");
    }

    #[test]
    fn test_struct_field_not_found() {
        let mut map = RegionMap::new();
        let pt = map.bind_owned("p", struct_point_ty(), SymbolicValue::Symbol("p".into()));
        let err = map.field_access(pt, "z").expect_err("no field z");
        assert!(matches!(err, RegionError::FieldNotFound { .. }));
    }

    // --- Array access ---

    #[test]
    fn test_array_access_in_bounds() {
        let mut map = RegionMap::new();
        let arr = map.bind_owned("arr", array_i32_ty(4), SymbolicValue::Symbol("arr".into()));
        let e0 = map.array_access(arr, 0).expect("elem 0");
        let e3 = map.array_access(arr, 3).expect("elem 3");
        assert_ne!(e0, e3);

        let v0 = map.read(e0).expect("read elem 0");
        assert_eq!(*v0, SymbolicValue::Symbol("arr_elem_0".into()));
    }

    #[test]
    fn test_array_access_out_of_bounds() {
        let mut map = RegionMap::new();
        let arr = map.bind_owned("arr", array_i32_ty(4), SymbolicValue::Symbol("arr".into()));
        let err = map.array_access(arr, 4).expect_err("out of bounds");
        assert!(matches!(err, RegionError::ArrayIndexOutOfBounds { index: 4, length: 4, .. }));
    }

    #[test]
    fn test_array_access_idempotent() {
        let mut map = RegionMap::new();
        let arr = map.bind_owned("arr", array_i32_ty(4), SymbolicValue::Symbol("arr".into()));
        let e1a = map.array_access(arr, 1).expect("first access");
        let e1b = map.array_access(arr, 1).expect("second access");
        assert_eq!(e1a, e1b);
    }

    // --- SMT encoding ---

    #[test]
    fn test_smt_var_name() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        assert_eq!(map.smt_var_name(id), Some("x".into()));
    }

    #[test]
    fn test_smt_sort() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        assert_eq!(map.smt_sort(id), Some(Sort::BitVec(32)));
    }

    #[test]
    fn test_to_formula_var() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let formula = map.to_formula_var(id).expect("formula");
        assert_eq!(formula, Formula::Var("x".into(), Sort::BitVec(32)));
    }

    #[test]
    fn test_array_bounds_check_formula() {
        let mut map = RegionMap::new();
        let arr = map.bind_owned("arr", array_i32_ty(4), SymbolicValue::Symbol("arr".into()));
        let idx = Formula::Var("i".into(), Sort::Int);
        let formula = map.array_bounds_check_formula(arr, &idx).expect("bounds formula");
        // Should be: (i < 0) OR (i >= 4)
        match &formula {
            Formula::Or(clauses) => assert_eq!(clauses.len(), 2),
            other => panic!("expected Or, got {other:?}"),
        }
    }

    // --- Region counting ---

    #[test]
    fn test_live_region_count() {
        let mut map = RegionMap::new();
        assert_eq!(map.live_region_count(), 0);
        let id = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        assert_eq!(map.live_region_count(), 1);
        map.drop_region(id).expect("drop");
        assert_eq!(map.live_region_count(), 0);
        assert_eq!(map.total_region_count(), 1);
    }

    // --- Write with active borrow ---

    #[test]
    fn test_write_to_owned_with_active_borrow_fails() {
        let mut map = RegionMap::new();
        let owner = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _borrow = map.borrow_shared("ref_x", owner).expect("borrow");
        let err = map.write(owner, SymbolicValue::Concrete(2)).expect_err("write while borrowed");
        assert!(matches!(err, RegionError::ExclusivityViolation { .. }));
    }

    // --- Borrow of moved fails ---

    #[test]
    fn test_borrow_of_moved_fails() {
        let mut map = RegionMap::new();
        let src = map.bind_owned("x", i32_ty(), SymbolicValue::Concrete(1));
        let _dest = map.move_value(src, "y").expect("move");
        let err = map.borrow_shared("ref_x", src).expect_err("borrow moved");
        assert!(matches!(err, RegionError::BorrowOfMoved { .. }));
    }

    // --- Default ---

    #[test]
    fn test_region_map_default() {
        let map = RegionMap::default();
        assert_eq!(map.live_region_count(), 0);
        assert_eq!(map.current_scope(), 0);
    }

    // --- Ownership kind display ---

    #[test]
    fn test_ownership_kind_display() {
        assert_eq!(OwnershipKind::Owned.to_string(), "owned");
        assert_eq!(OwnershipKind::SharedBorrow.to_string(), "&");
        assert_eq!(OwnershipKind::MutBorrow.to_string(), "&mut");
    }

    // --- Region state display ---

    #[test]
    fn test_region_state_display() {
        assert_eq!(RegionState::Live.to_string(), "live");
        assert_eq!(RegionState::Moved.to_string(), "moved");
        assert_eq!(RegionState::Dropped.to_string(), "dropped");
        assert_eq!(RegionState::Expired.to_string(), "expired");
    }

    // --- Complex scenario: clamp function ---

    #[test]
    fn test_clamp_scenario() {
        // Simulates: fn clamp(x: i32, lo: i32, hi: i32) -> i32
        let mut map = RegionMap::new();
        let x_id = map.bind_param("x", i32_ty());
        let lo_id = map.bind_param("lo", i32_ty());
        let hi_id = map.bind_param("hi", i32_ty());

        // Read all params.
        let x = map.read(x_id).expect("read x").clone();
        let lo = map.read(lo_id).expect("read lo").clone();
        let hi = map.read(hi_id).expect("read hi").clone();

        // Create result: if x < lo then lo; if x > hi then hi; else x
        let result = SymbolicValue::ite(
            SymbolicValue::bin_op(x.clone(), trust_types::BinOp::Lt, lo.clone()),
            lo.clone(),
            SymbolicValue::ite(
                SymbolicValue::bin_op(x.clone(), trust_types::BinOp::Gt, hi.clone()),
                hi.clone(),
                x.clone(),
            ),
        );

        let _ret = map.bind_owned("_ret", i32_ty(), result);
        assert_eq!(map.live_region_count(), 4); // x, lo, hi, _ret
    }

    // --- Complex scenario: struct with borrow and drop ---

    #[test]
    fn test_struct_borrow_field_read_drop() {
        let mut map = RegionMap::new();
        let pt = map.bind_owned("p", struct_point_ty(), SymbolicValue::Symbol("p".into()));

        // Borrow the struct.
        map.enter_scope();
        let borrow = map.borrow_shared("ref_p", pt).expect("borrow struct");

        // Access field through borrow.
        let borrow_region = map.get_region(borrow).expect("get borrow");
        assert_eq!(borrow_region.ownership(), OwnershipKind::SharedBorrow);

        // Exit scope expires borrow.
        map.exit_scope();

        // Now we can drop the struct.
        map.drop_region(pt).expect("drop struct");
        assert_eq!(map.live_region_count(), 0);
    }

    // --- u64 type test ---

    #[test]
    fn test_u64_region() {
        let mut map = RegionMap::new();
        let id = map.bind_owned("n", u64_ty(), SymbolicValue::Symbol("n".into()));
        assert_eq!(map.smt_sort(id), Some(Sort::BitVec(64)));
    }
}
