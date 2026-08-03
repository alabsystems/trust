// trust_vcgen/memory_provenance.rs: Provenance-based VC generation (Layer 2)
//
// Implements Stacked Borrows provenance tracking as verification conditions.
// Analyzes pointer borrows through MIR to detect:
// - Use of invalidated borrows (popped from borrow stack)
// - Writes through shared references
// - Use-after-free via provenance tracking
// - Provenance mismatch (accessing memory through unrelated pointer)
//
// Part of #150: Memory model Layers 2-3
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::provenance::*;
use trust_types::*;

// ────────────────────────────────────────────────────────────────────────────
// Borrow stack: Stacked Borrows model
// ────────────────────────────────────────────────────────────────────────────

/// A borrow stack for a single memory location (allocation).
///
/// Implements the Stacked Borrows model: each access through a pointer tag
/// pops everything above that tag, enforcing a stack discipline on borrows.
/// A `SharedRef` entry can coexist with other `SharedRef` entries but a
/// `MutableRef` entry invalidates everything above it on use.
#[derive(Debug, Clone)]
pub struct BorrowStack {
    /// The allocation this stack belongs to.
    region_tag: ProvenanceTag,
    /// Stack entries, bottom to top (last = top).
    stack: Vec<BorrowEntry>,
    /// Next tag to assign.
    next_tag: u64,
    /// Violations detected during stack operations.
    violations: Vec<ProvenanceViolation>,
}

impl BorrowStack {
    /// Create a new borrow stack for a region.
    #[must_use]
    pub fn new(region_tag: ProvenanceTag, initial_tag: ProvenanceTag, kind: BorrowKind) -> Self {
        Self {
            region_tag,
            stack: vec![BorrowEntry { tag: initial_tag, kind, span: SourceSpan::default() }],
            next_tag: initial_tag.0 + 1,
            violations: Vec::new(),
        }
    }

    /// Push a new borrow onto the stack, returning its tag.
    pub fn push_borrow(&mut self, kind: BorrowKind, span: SourceSpan) -> ProvenanceTag {
        let tag = ProvenanceTag(self.next_tag);
        self.next_tag += 1;
        self.stack.push(BorrowEntry { tag, kind, span });
        tag
    }

    /// Record a read access through the given tag.
    ///
    /// In Stacked Borrows, a read through tag T:
    /// - Finds T in the stack
    /// - If T is `MutableRef`: pops everything above T
    /// - If T is `SharedRef`/`RawShared`: keeps items above T
    /// - If T is not found: violation
    pub fn access_read(&mut self, tag: ProvenanceTag, span: &SourceSpan) {
        if tag == ProvenanceTag::WILDCARD {
            return; // wildcard always succeeds
        }

        let pos = self.stack.iter().rposition(|e| e.tag == tag);
        match pos {
            Some(_) => {
                // Tag found -- read succeeds (no pop for shared reads).
            }
            None => {
                self.violations.push(ProvenanceViolation {
                    kind: ProvenanceViolationKind::InvalidatedBorrow,
                    tag,
                    span: span.clone(),
                    message: format!(
                        "read through {} failed: tag not in borrow stack for {}",
                        tag, self.region_tag
                    ),
                });
            }
        }
    }

    /// Record a write access through the given tag.
    ///
    /// In Stacked Borrows, a write through tag T:
    /// - Finds T in the stack
    /// - Verifies T has write permission
    /// - Pops everything above T
    /// - If T not found or lacks write permission: violation
    pub fn access_write(&mut self, tag: ProvenanceTag, span: &SourceSpan) {
        if tag == ProvenanceTag::WILDCARD {
            return;
        }

        let pos = self.stack.iter().rposition(|e| e.tag == tag);
        match pos {
            Some(idx) => {
                let entry = &self.stack[idx];
                if !entry.kind.permits_write() {
                    self.violations.push(ProvenanceViolation {
                        kind: ProvenanceViolationKind::WriteThroughSharedRef,
                        tag,
                        span: span.clone(),
                        message: format!(
                            "write through {} ({}) is not permitted",
                            tag,
                            entry.kind.label()
                        ),
                    });
                } else {
                    // Pop everything above this entry.
                    self.stack.truncate(idx + 1);
                }
            }
            None => {
                self.violations.push(ProvenanceViolation {
                    kind: ProvenanceViolationKind::InvalidatedBorrow,
                    tag,
                    span: span.clone(),
                    message: format!(
                        "write through {} failed: tag not in borrow stack for {}",
                        tag, self.region_tag
                    ),
                });
            }
        }
    }

    /// Get all violations detected so far.
    #[must_use]
    pub fn violations(&self) -> &[ProvenanceViolation] {
        &self.violations
    }

    /// Current stack depth.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.stack.len()
    }

    /// Whether a tag is currently valid (present in the stack).
    #[must_use]
    pub fn is_tag_valid(&self, tag: ProvenanceTag) -> bool {
        tag == ProvenanceTag::WILDCARD || self.stack.iter().any(|e| e.tag == tag)
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Provenance tracker
// ────────────────────────────────────────────────────────────────────────────

/// Tracks provenance across all memory regions in a function.
///
/// Maps each allocation to its borrow stack, and each pointer local to its
/// current provenance tag and region association.
#[derive(Debug, Clone)]
pub struct ProvenanceTracker {
    /// Borrow stacks, keyed by region tag.
    stacks: FxHashMap<ProvenanceTag, BorrowStack>,
    /// Map from local index to (region_tag, current_tag).
    local_provenance: FxHashMap<usize, (ProvenanceTag, ProvenanceTag)>,
    /// Regions that have been freed.
    freed_regions: FxHashMap<ProvenanceTag, SourceSpan>,
    /// Next region tag to assign.
    next_region_tag: u64,
}

impl ProvenanceTracker {
    /// Create a new empty tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            stacks: FxHashMap::default(),
            local_provenance: FxHashMap::default(),
            freed_regions: FxHashMap::default(),
            next_region_tag: 1,
        }
    }

    /// Register a new allocation, returning its region tag.
    pub fn new_allocation(&mut self, kind: BorrowKind) -> ProvenanceTag {
        let region_tag = ProvenanceTag(self.next_region_tag);
        self.next_region_tag += 1;
        let stack = BorrowStack::new(region_tag, region_tag, kind);
        self.stacks.insert(region_tag, stack);
        region_tag
    }

    /// Create a borrow of an existing region, binding it to a local.
    pub fn create_borrow(
        &mut self,
        local: usize,
        region_tag: ProvenanceTag,
        kind: BorrowKind,
        span: SourceSpan,
    ) -> Option<ProvenanceTag> {
        let stack = self.stacks.get_mut(&region_tag)?;
        let new_tag = stack.push_borrow(kind, span);
        self.local_provenance.insert(local, (region_tag, new_tag));
        Some(new_tag)
    }

    /// Bind a local to an existing provenance (e.g., copy/move).
    pub fn bind_local(&mut self, dest: usize, region_tag: ProvenanceTag, tag: ProvenanceTag) {
        self.local_provenance.insert(dest, (region_tag, tag));
    }

    /// Record a read through a local's pointer.
    pub fn read_through(&mut self, local: usize, span: &SourceSpan) -> Vec<ProvenanceViolation> {
        let mut violations = Vec::new();

        if let Some(&(region_tag, ptr_tag)) = self.local_provenance.get(&local) {
            // Check for use-after-free.
            if let Some(free_span) = self.freed_regions.get(&region_tag) {
                violations.push(ProvenanceViolation {
                    kind: ProvenanceViolationKind::UseAfterFree,
                    tag: ptr_tag,
                    span: span.clone(),
                    message: format!(
                        "read through {} accesses freed region {} (freed at {}:{})",
                        ptr_tag, region_tag, free_span.file, free_span.line_start
                    ),
                });
            }

            if let Some(stack) = self.stacks.get_mut(&region_tag) {
                stack.access_read(ptr_tag, span);
                violations.extend_from_slice(stack.violations());
            }
        }

        violations
    }

    /// Record a write through a local's pointer.
    pub fn write_through(&mut self, local: usize, span: &SourceSpan) -> Vec<ProvenanceViolation> {
        let mut violations = Vec::new();

        if let Some(&(region_tag, ptr_tag)) = self.local_provenance.get(&local) {
            if let Some(free_span) = self.freed_regions.get(&region_tag) {
                violations.push(ProvenanceViolation {
                    kind: ProvenanceViolationKind::UseAfterFree,
                    tag: ptr_tag,
                    span: span.clone(),
                    message: format!(
                        "write through {} accesses freed region {} (freed at {}:{})",
                        ptr_tag, region_tag, free_span.file, free_span.line_start
                    ),
                });
            }

            if let Some(stack) = self.stacks.get_mut(&region_tag) {
                stack.access_write(ptr_tag, span);
                violations.extend_from_slice(stack.violations());
            }
        }

        violations
    }

    /// Mark a region as freed.
    pub fn free_region(&mut self, region_tag: ProvenanceTag, span: SourceSpan) {
        self.freed_regions.insert(region_tag, span);
    }

    /// Get the provenance info for a local, if tracked.
    #[must_use]
    pub fn local_provenance(&self, local: usize) -> Option<(ProvenanceTag, ProvenanceTag)> {
        self.local_provenance.get(&local).copied()
    }

    /// Number of tracked regions.
    #[must_use]
    pub fn region_count(&self) -> usize {
        self.stacks.len()
    }

    /// Number of tracked locals.
    #[must_use]
    pub fn local_count(&self) -> usize {
        self.local_provenance.len()
    }
}

impl Default for ProvenanceTracker {
    fn default() -> Self {
        Self::new()
    }
}

// ────────────────────────────────────────────────────────────────────────────
// VC generation from provenance analysis
// ────────────────────────────────────────────────────────────────────────────

/// Analyze a function for provenance violations and generate VCs.
///
/// Walks the MIR forward, tracking borrows through the Stacked Borrows model.
/// For each violation detected, generates a VC that is always SAT (definite
/// violation) or encodes a conditional check.
#[must_use]
pub fn check_provenance(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let mut tracker = ProvenanceTracker::new();
    let mut vcs = Vec::new();

    // Initialize: ref-typed arguments get fresh allocations.
    for local in &func.body.locals {
        if local.index <= func.body.arg_count
            && let Ty::Ref { mutable, .. } = &local.ty
        {
            let kind = if *mutable { BorrowKind::MutableRef } else { BorrowKind::SharedRef };
            let region_tag = tracker.new_allocation(kind);
            tracker.bind_local(local.index, region_tag, region_tag);
        }
    }

    // Forward walk through blocks.
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, span } = stmt {
                process_assignment(&mut tracker, func, place, rvalue, span, &mut vcs);
            }
        }

        // Handle Drop terminators (deallocation).
        if let Terminator::Drop { place, span, .. } = &block.terminator
            && let Some(&(region_tag, _)) = tracker.local_provenance.get(&place.local).as_ref()
        {
            tracker.free_region(*region_tag, span.clone());
        }
    }

    vcs
}

/// Process a single assignment statement for provenance tracking.
fn process_assignment(
    tracker: &mut ProvenanceTracker,
    func: &VerifiableFunction,
    place: &Place,
    rvalue: &Rvalue,
    span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    let dest = place.local;

    match rvalue {
        // Taking a reference creates a new borrow.
        Rvalue::Ref { mutable, place: src_place } => {
            let kind = if *mutable { BorrowKind::MutableRef } else { BorrowKind::SharedRef };

            // If the source is tracked, create a derived borrow.
            if let Some(&(region_tag, _)) = tracker.local_provenance.get(&src_place.local).as_ref()
            {
                tracker.create_borrow(dest, *region_tag, kind, span.clone());
            } else {
                // Source not tracked yet -- create a new allocation.
                let region_tag = tracker.new_allocation(kind);
                tracker.bind_local(dest, region_tag, region_tag);
            }
        }

        // Copy/Move propagates provenance.
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
            let has_deref = src.projections.iter().any(|p| matches!(p, Projection::Deref));

            if has_deref {
                // Dereferencing: this is a read access through the pointer.
                let violations = tracker.read_through(src.local, span);
                emit_provenance_vcs(func, &violations, vcs);
            } else if let Some(&(region_tag, tag)) =
                tracker.local_provenance.get(&src.local).as_ref()
            {
                tracker.bind_local(dest, *region_tag, *tag);
            }
        }

        // Writes through deref projections on the destination side.
        _ => {
            let has_deref = place.projections.iter().any(|p| matches!(p, Projection::Deref));
            if has_deref {
                let violations = tracker.write_through(place.local, span);
                emit_provenance_vcs(func, &violations, vcs);
            }
        }
    }
}

/// Convert provenance violations into verification conditions.
fn emit_provenance_vcs(
    func: &VerifiableFunction,
    violations: &[ProvenanceViolation],
    vcs: &mut Vec<VerificationCondition>,
) {
    for violation in violations {
        let kind_label = violation.kind.label();
        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!("[provenance] {kind_label}: {}", violation.message),
            },
            function: func.name.as_str().into(),
            location: violation.span.clone(),
            formula: Formula::Bool(true), // definite violation
            contract_metadata: None,
            obligation: None,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── BorrowStack tests ─────────────────────────────────────────────────

    #[test]
    fn test_borrow_stack_new() {
        let stack = BorrowStack::new(ProvenanceTag(1), ProvenanceTag(1), BorrowKind::MutableRef);
        assert_eq!(stack.depth(), 1);
        assert!(stack.is_tag_valid(ProvenanceTag(1)));
        assert!(stack.violations().is_empty());
    }

    #[test]
    fn test_borrow_stack_push_and_read() {
        let mut stack =
            BorrowStack::new(ProvenanceTag(1), ProvenanceTag(1), BorrowKind::MutableRef);
        let tag2 = stack.push_borrow(BorrowKind::SharedRef, SourceSpan::default());

        assert_eq!(stack.depth(), 2);
        assert!(stack.is_tag_valid(tag2));
        assert!(stack.is_tag_valid(ProvenanceTag(1)));

        // Reading through tag2 should succeed.
        stack.access_read(tag2, &SourceSpan::default());
        assert!(stack.violations().is_empty());
    }

    #[test]
    fn test_borrow_stack_write_pops_above() {
        let mut stack =
            BorrowStack::new(ProvenanceTag(1), ProvenanceTag(1), BorrowKind::MutableRef);
        let tag2 = stack.push_borrow(BorrowKind::MutableRef, SourceSpan::default());
        let tag3 = stack.push_borrow(BorrowKind::SharedRef, SourceSpan::default());

        assert_eq!(stack.depth(), 3);

        // Write through tag2 should pop tag3.
        stack.access_write(tag2, &SourceSpan::default());
        assert_eq!(stack.depth(), 2);
        assert!(stack.is_tag_valid(tag2));
        assert!(!stack.is_tag_valid(tag3));
    }

    #[test]
    fn test_borrow_stack_write_through_shared_ref_violation() {
        let mut stack =
            BorrowStack::new(ProvenanceTag(1), ProvenanceTag(1), BorrowKind::MutableRef);
        let shared_tag = stack.push_borrow(BorrowKind::SharedRef, SourceSpan::default());

        stack.access_write(shared_tag, &SourceSpan::default());
        assert_eq!(stack.violations().len(), 1);
        assert_eq!(stack.violations()[0].kind, ProvenanceViolationKind::WriteThroughSharedRef);
    }

    #[test]
    fn test_borrow_stack_read_invalidated_tag() {
        let mut stack =
            BorrowStack::new(ProvenanceTag(1), ProvenanceTag(1), BorrowKind::MutableRef);
        let tag2 = stack.push_borrow(BorrowKind::MutableRef, SourceSpan::default());
        let _tag3 = stack.push_borrow(BorrowKind::MutableRef, SourceSpan::default());

        // Write through tag2 invalidates tag3.
        stack.access_write(tag2, &SourceSpan::default());

        // Now reading through tag3 should fail.
        stack.access_read(ProvenanceTag(3), &SourceSpan::default());
        // Violations include the one from the read attempt.
        assert!(
            stack.violations().iter().any(|v| v.kind == ProvenanceViolationKind::InvalidatedBorrow)
        );
    }

    #[test]
    fn test_borrow_stack_wildcard_always_succeeds() {
        let mut stack =
            BorrowStack::new(ProvenanceTag(1), ProvenanceTag(1), BorrowKind::MutableRef);
        stack.access_read(ProvenanceTag::WILDCARD, &SourceSpan::default());
        stack.access_write(ProvenanceTag::WILDCARD, &SourceSpan::default());
        assert!(stack.violations().is_empty());
    }

    // ── ProvenanceTracker tests ───────────────────────────────────────────

    #[test]
    fn test_tracker_new_allocation() {
        let mut tracker = ProvenanceTracker::new();
        let tag1 = tracker.new_allocation(BorrowKind::MutableRef);
        let tag2 = tracker.new_allocation(BorrowKind::SharedRef);

        assert_ne!(tag1, tag2);
        assert_eq!(tracker.region_count(), 2);
    }

    #[test]
    fn test_tracker_create_borrow() {
        let mut tracker = ProvenanceTracker::new();
        let region = tracker.new_allocation(BorrowKind::MutableRef);
        tracker.bind_local(0, region, region);

        let borrow_tag =
            tracker.create_borrow(1, region, BorrowKind::SharedRef, SourceSpan::default());
        assert!(borrow_tag.is_some());

        let (r, t) = tracker.local_provenance(1).expect("local 1 tracked");
        assert_eq!(r, region);
        assert_ne!(t, region); // derived tag
    }

    #[test]
    fn test_tracker_read_through_valid() {
        let mut tracker = ProvenanceTracker::new();
        let region = tracker.new_allocation(BorrowKind::MutableRef);
        tracker.bind_local(0, region, region);

        let violations = tracker.read_through(0, &SourceSpan::default());
        assert!(violations.is_empty());
    }

    #[test]
    fn test_tracker_use_after_free() {
        let mut tracker = ProvenanceTracker::new();
        let region = tracker.new_allocation(BorrowKind::MutableRef);
        tracker.bind_local(0, region, region);
        tracker.free_region(region, SourceSpan::default());

        let violations = tracker.read_through(0, &SourceSpan::default());
        assert!(violations.iter().any(|v| v.kind == ProvenanceViolationKind::UseAfterFree));
    }

    #[test]
    fn test_tracker_local_count() {
        let mut tracker = ProvenanceTracker::new();
        let r1 = tracker.new_allocation(BorrowKind::MutableRef);
        let r2 = tracker.new_allocation(BorrowKind::SharedRef);
        tracker.bind_local(0, r1, r1);
        tracker.bind_local(1, r2, r2);

        assert_eq!(tracker.local_count(), 2);
    }

    // ── check_provenance integration tests ────────────────────────────────

    #[test]
    fn test_check_provenance_safe_function() {
        // Function with no pointer operations should produce no VCs.
        let func = VerifiableFunction {
            name: "safe_add".into(),
            def_path: "test::safe_add".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = check_provenance(&func);
        assert!(vcs.is_empty(), "safe function should produce no provenance VCs");
    }

    #[test]
    fn test_check_provenance_ref_borrow_and_read() {
        // fn f(x: &u32) -> u32 { *x }
        // Takes a ref arg, reads through it -- should be fine.
        let func = VerifiableFunction {
            name: "read_ref".into(),
            def_path: "test::read_ref".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("x".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = check_provenance(&func);
        assert!(vcs.is_empty(), "reading through a valid ref should produce no VCs");
    }

    #[test]
    fn test_check_provenance_detects_write_through_shared() {
        // fn f(x: &u32) { *x = 5; }
        // Writing through a shared ref should produce a violation.
        let func = VerifiableFunction {
            name: "write_shared".into(),
            def_path: "test::write_shared".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("x".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = check_provenance(&func);
        assert!(!vcs.is_empty(), "write through shared ref should produce VC");
        assert!(vcs.iter().any(|vc| {
            if let VcKind::Assertion { message } = &vc.kind {
                message.contains("write through shared ref")
            } else {
                false
            }
        }));
    }

    #[test]
    fn test_check_provenance_mutable_ref_write_ok() {
        // fn f(x: &mut u32) { *x = 5; }
        // Writing through a mutable ref is fine.
        let func = VerifiableFunction {
            name: "write_mut".into(),
            def_path: "test::write_mut".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                        name: Some("x".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = check_provenance(&func);
        assert!(vcs.is_empty(), "write through mutable ref should produce no VCs");
    }

    #[test]
    fn test_check_provenance_vcs_are_l0_safety() {
        // All provenance VCs should be L0Safety (assertion kind).
        let func = VerifiableFunction {
            name: "write_shared".into(),
            def_path: "test::write_shared".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("x".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = check_provenance(&func);
        for vc in &vcs {
            assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
        }
    }
}
