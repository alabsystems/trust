// trust_vcgen/separation_logic/heap.rs: Symbolic heap for separation logic reasoning
//
// Tracks heap cells (PointsTo assertions) and pointer provenance. Supports
// heap operations (read, write, allocate, free) and generates the
// corresponding separation logic formulas and verification conditions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

use super::encoding::sep_to_formula;
use super::formula::SepFormula;
use super::provenance::{PointerPermission, ProvenanceId, SymbolicPointer};
use super::vc_gen::{deref_vc, raw_write_vc};

// ────────────────────────────────────────────────────────────────────────────
// Symbolic heap
// ────────────────────────────────────────────────────────────────────────────

/// A symbolic heap for separation logic reasoning.
///
/// Tracks heap cells (PointsTo assertions) and pointer provenance. Supports
/// heap operations (read, write, allocate, free) and generates the
/// corresponding separation logic formulas and verification conditions.
///
/// The heap is modeled as an SMT array `(Array Int Int)` and each cell
/// is a `PointsTo { addr, value }` in the symbolic heap fragment.
#[derive(Debug, Clone)]
pub struct SymbolicHeap {
    /// The SMT variable name for the heap array.
    heap_var: String,
    /// Tracked heap cells: addr -> value.
    cells: FxHashMap<String, HeapCell>,
    /// Tracked pointers with provenance.
    pointers: FxHashMap<String, SymbolicPointer>,
    /// Next provenance ID to assign.
    next_provenance: u64,
    /// Freed provenance IDs.
    freed_provenances: Vec<ProvenanceId>,
}

/// A single heap cell in the symbolic heap.
#[derive(Debug, Clone)]
pub struct HeapCell {
    /// The address formula for this cell.
    pub addr: Formula,
    /// The current value formula for this cell.
    pub value: Formula,
    /// The provenance of the allocation containing this cell.
    pub provenance: ProvenanceId,
}

impl SymbolicHeap {
    /// Create a new empty symbolic heap.
    #[must_use]
    pub fn new(heap_var: &str) -> Self {
        Self {
            heap_var: heap_var.to_string(),
            cells: FxHashMap::default(),
            pointers: FxHashMap::default(),
            next_provenance: 1,
            freed_provenances: Vec::new(),
        }
    }

    /// Allocate a fresh region and return its provenance ID.
    pub fn allocate(&mut self, name: &str) -> ProvenanceId {
        let id = ProvenanceId(self.next_provenance);
        self.next_provenance += 1;
        let ptr = SymbolicPointer::new(name, id, PointerPermission::ReadWrite);
        self.pointers.insert(name.to_string(), ptr);
        id
    }

    /// Track a pointer with an existing provenance.
    pub fn track_pointer(&mut self, ptr: SymbolicPointer) {
        self.pointers.insert(ptr.name.clone(), ptr);
    }

    /// Write a cell to the heap.
    pub fn write_cell(&mut self, name: &str, addr: Formula, value: Formula, prov: ProvenanceId) {
        self.cells.insert(name.to_string(), HeapCell { addr, value, provenance: prov });
    }

    /// Free an allocation by provenance.
    pub fn free(&mut self, prov: ProvenanceId) {
        self.freed_provenances.push(prov);
        // Mark any pointers with this provenance as freed.
        for ptr in self.pointers.values_mut() {
            if ptr.provenance == prov {
                ptr.permission = PointerPermission::Freed;
            }
        }
    }

    /// Look up a tracked pointer by name.
    #[must_use]
    pub fn pointer(&self, name: &str) -> Option<&SymbolicPointer> {
        self.pointers.get(name)
    }

    /// Number of tracked cells.
    #[must_use]
    pub fn cell_count(&self) -> usize {
        self.cells.len()
    }

    /// Number of tracked pointers.
    #[must_use]
    pub fn pointer_count(&self) -> usize {
        self.pointers.len()
    }

    /// Whether a provenance has been freed.
    #[must_use]
    pub fn is_freed(&self, prov: ProvenanceId) -> bool {
        self.freed_provenances.contains(&prov)
    }

    /// Convert the current heap state to a separation logic formula.
    ///
    /// Produces `cell_1 * cell_2 * ... * cell_n` (separating conjunction
    /// of all tracked cells). If the heap is empty, returns `emp`.
    #[must_use]
    pub fn to_sep_formula(&self) -> SepFormula {
        let cells: Vec<SepFormula> = self
            .cells
            .values()
            .map(|cell| SepFormula::points_to(cell.addr.clone(), cell.value.clone()))
            .collect();
        SepFormula::star_many(cells)
    }

    /// Translate the entire heap to a FOL formula.
    #[must_use]
    pub fn to_formula(&self) -> Formula {
        sep_to_formula(&self.to_sep_formula(), &self.heap_var)
    }

    /// Generate VCs for a read through a tracked pointer.
    ///
    /// Checks: non-null, valid allocation, not freed, read permission.
    #[must_use]
    pub fn read_vc(
        &self,
        ptr_name: &str,
        func_name: &str,
        span: &SourceSpan,
    ) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();

        if let Some(ptr) = self.pointers.get(ptr_name) {
            // Check for use-after-free.
            if self.is_freed(ptr.provenance) {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:heap] use-after-free: read through freed pointer `{ptr_name}`"
                        ),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Bool(true), // definite violation
                    contract_metadata: None,
                    obligation: None,
                });
                return vcs;
            }

            // Check permission.
            if !ptr.permission.can_read() {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:heap] permission denied: read through `{ptr_name}` ({})",
                            ptr.permission.label()
                        ),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });
            }

            // Provenance bounds check.
            if ptr.provenance.is_concrete() {
                let bounds = ptr.in_bounds_formula();
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:heap] out-of-bounds: read through `{ptr_name}` outside {}'s allocation",
                            ptr.provenance
                        ),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(bounds)),
                    contract_metadata: None,
                    obligation: None,
                });
            }
        }

        // Delegate to deref_vc for standard null/alloc/align checks.
        vcs.extend(deref_vc(func_name, ptr_name, span));
        vcs
    }

    /// Generate VCs for a write through a tracked pointer.
    ///
    /// Checks: all read checks plus write permission.
    #[must_use]
    pub fn write_vc(
        &self,
        ptr_name: &str,
        value_formula: &Formula,
        func_name: &str,
        span: &SourceSpan,
    ) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();

        if let Some(ptr) = self.pointers.get(ptr_name) {
            // Check for use-after-free.
            if self.is_freed(ptr.provenance) {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:heap] use-after-free: write through freed pointer `{ptr_name}`"
                        ),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });
                return vcs;
            }

            // Check write permission.
            if !ptr.permission.can_write() {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:heap] permission denied: write through `{ptr_name}` ({})",
                            ptr.permission.label()
                        ),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });
            }
        }

        // Delegate to raw_write_vc for standard deref + write checks.
        vcs.extend(raw_write_vc(func_name, ptr_name, value_formula, span));
        vcs
    }
}
