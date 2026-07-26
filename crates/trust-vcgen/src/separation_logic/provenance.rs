// trust_vcgen/separation_logic/provenance.rs: Provenance tracking for raw pointers
//
// Implements ProvenanceId, SymbolicPointer, and PointerPermission for tracking
// pointer origins and permissions in separation logic reasoning.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

// ────────────────────────────────────────────────────────────────────────────
// Provenance tracking for raw pointers
// ────────────────────────────────────────────────────────────────────────────

/// A unique provenance identifier for tracking pointer origins in separation logic.
///
/// Each allocation produces a fresh `ProvenanceId`. Pointers derived from
/// different allocations carry different provenance, and the separation logic
/// engine uses this to enforce that pointers with different provenance cannot
/// alias (i.e., they point into disjoint heap regions).
///
/// This complements the Stacked Borrows model in `memory_provenance.rs` by
/// encoding provenance constraints as separation logic formulas that can be
/// dispatched to SMT solvers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProvenanceId(pub u64);

impl ProvenanceId {
    /// The unknown/wildcard provenance (matches any allocation).
    pub const UNKNOWN: Self = Self(0);

    /// Whether this provenance is concrete (not unknown).
    #[must_use]
    pub fn is_concrete(self) -> bool {
        self.0 != 0
    }

    /// SMT variable name for this provenance's base address.
    #[must_use]
    pub fn base_var(&self) -> String {
        super::generated_symbol(&format!("prov_{}_base", self.0))
    }

    /// SMT variable name for this provenance's allocation size.
    #[must_use]
    pub fn size_var(&self) -> String {
        super::generated_symbol(&format!("prov_{}_size", self.0))
    }
}

impl std::fmt::Display for ProvenanceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == 0 { write!(f, "prov(*)") } else { write!(f, "prov({})", self.0) }
    }
}

/// A symbolic pointer with provenance tracking.
///
/// Associates a pointer formula (the address value) with its provenance
/// (which allocation it was derived from) and permission level. This is
/// the bridge between separation logic heap reasoning and Rust's
/// ownership/borrow model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicPointer {
    /// The address formula (SMT-level representation of the pointer value).
    pub addr: Formula,
    /// Which allocation this pointer was derived from.
    pub provenance: ProvenanceId,
    /// Human-readable name for diagnostics.
    pub name: String,
    /// Permission level for this pointer.
    pub permission: PointerPermission,
}

/// Permission level for a symbolic pointer.
///
/// Maps to Rust's borrow semantics: read-only, read-write, or freed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PointerPermission {
    /// Read-only access (shared reference or `*const T`).
    ReadOnly,
    /// Read-write access (mutable reference or `*mut T`).
    ReadWrite,
    /// The allocation has been freed; any access is UB.
    Freed,
}

impl PointerPermission {
    /// Whether this permission allows reads.
    #[must_use]
    pub fn can_read(self) -> bool {
        matches!(self, Self::ReadOnly | Self::ReadWrite)
    }

    /// Whether this permission allows writes.
    #[must_use]
    pub fn can_write(self) -> bool {
        matches!(self, Self::ReadWrite)
    }

    /// Human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::ReadOnly => "read-only",
            Self::ReadWrite => "read-write",
            Self::Freed => "freed",
        }
    }
}

impl SymbolicPointer {
    /// Create a new symbolic pointer.
    #[must_use]
    pub fn new(name: &str, provenance: ProvenanceId, permission: PointerPermission) -> Self {
        Self {
            addr: Formula::Var(super::generated_symbol(&format!("ptr_{name}")), Sort::Int),
            provenance,
            name: name.to_string(),
            permission,
        }
    }

    /// Generate a provenance-bounded validity formula.
    ///
    /// Asserts that this pointer's address falls within the allocation
    /// identified by its provenance: `base <= addr < base + size`.
    #[must_use]
    pub fn in_bounds_formula(&self) -> Formula {
        if !self.provenance.is_concrete() {
            // Unknown provenance: cannot assert bounds.
            return Formula::Bool(true);
        }
        let base = Formula::Var(self.provenance.base_var(), Sort::Int);
        let size = Formula::Var(self.provenance.size_var(), Sort::Int);
        Formula::And(vec![
            // base <= addr
            Formula::Le(Box::new(base.clone()), Box::new(self.addr.clone())),
            // addr < base + size
            Formula::Lt(
                Box::new(self.addr.clone()),
                Box::new(Formula::Add(Box::new(base), Box::new(size))),
            ),
        ])
    }

    /// Encode that this pointer's provenance matches a given allocation.
    ///
    /// Returns a formula asserting that the pointer address falls within
    /// the given allocation region `[alloc_base, alloc_base + alloc_size)`.
    #[must_use]
    pub fn provenance_matches(&self, alloc_base: &Formula, alloc_size: &Formula) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(alloc_base.clone()), Box::new(self.addr.clone())),
            Formula::Lt(
                Box::new(self.addr.clone()),
                Box::new(Formula::Add(Box::new(alloc_base.clone()), Box::new(alloc_size.clone()))),
            ),
        ])
    }
}
