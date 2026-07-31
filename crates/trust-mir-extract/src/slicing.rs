// trust-mir-extract/slicing.rs: Backward slicing for VC minimization
//
// Given a target statement (e.g., an assertion), computes the backward slice:
// the minimal set of statements that can affect the target's computation.
// This reduces the size of verification conditions sent to solvers.
//
// Inspired by angr's backward_slice.py (refs/angr/angr/analyses/backward_slice.py).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// this compiler-internal VC minimization scaffold is compiled and
// unit-tested before the extraction pipeline wires it into production use.
#![allow(dead_code)]
// Hash-set iteration is confined to dependency closure construction; public
// slice membership is stored in BTreeSet and is not used as a rustc query key.
#![allow(rustc::potential_query_instability)]

use std::collections::{BTreeSet, VecDeque};

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    BlockId, Operand, Place, Projection, Rvalue, Statement, Terminator, VerifiableBody,
};

/// A location within a function body: (block index, statement index within that block).
/// For terminators, stmt_index == block's stmts.len() (one past the last statement).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Location {
    pub block: usize,
    pub stmt_index: usize,
}

/// The result of backward slicing: which locations are in the slice.
#[derive(Debug, Clone)]
pub(crate) struct SliceResult {
    /// Set of (block, stmt_index) pairs that are in the backward slice.
    pub locations: BTreeSet<Location>,
}

impl SliceResult {
    /// Returns true if a given location is in the slice.
    pub(crate) fn contains(&self, block: usize, stmt_index: usize) -> bool {
        self.locations.contains(&Location { block, stmt_index })
    }

    /// Number of locations in the slice.
    pub(crate) fn len(&self) -> usize {
        self.locations.len()
    }

    /// Whether the slice is empty.
    pub(crate) fn is_empty(&self) -> bool {
        self.locations.is_empty()
    }
}

/// A sliced body: the original body with only slice-relevant statements retained.
/// Non-relevant statements are replaced with Nop.
#[derive(Debug, Clone)]
pub(crate) struct SlicedBody {
    /// The body with irrelevant statements replaced by Nop.
    pub body: VerifiableBody,
    /// The slice metadata.
    pub slice: SliceResult,
    /// How many statements were removed (replaced with Nop).
    pub removed_count: usize,
}

/// Dependency graph over a VerifiableBody.
///
/// Tracks two kinds of dependencies:
/// - **Data dependencies**: statement S2 depends on S1 if S1 writes to a place that S2 reads.
/// - **Control dependencies**: statement S depends on a branch if S is only reachable
///   through that branch.
#[derive(Debug)]
pub(crate) struct DependencyGraph {
    /// For each location, the set of locations it depends on (data + control).
    deps: FxHashMap<Location, FxHashSet<Location>>,
    /// For each block, its predecessor blocks (for control dependency).
    predecessors: FxHashMap<usize, Vec<usize>>,
    /// Number of blocks.
    num_blocks: usize,
}

impl DependencyGraph {
    /// Build a dependency graph from a VerifiableBody.
    pub(crate) fn build(body: &VerifiableBody) -> Self {
        let num_blocks = body.blocks.len();
        let predecessors = Self::compute_predecessors(body);
        let mut deps: FxHashMap<Location, FxHashSet<Location>> = FxHashMap::default();

        // For each block, track the last write to each local variable.
        // We process blocks in order; for cross-block deps we look at predecessor blocks.

        // First pass: compute conservative reaching-definition maps. We keep all
        // writes to a base local, not just the last one, because projected
        // writes like `_x.0` and `_x.1` cannot safely kill each other without a
        // place-sensitive memory model.
        let block_defs = Self::compute_block_defs(body);
        let reaching_defs = Self::compute_reaching_defs(num_blocks, &predecessors, &block_defs);
        let control_deps = Self::compute_control_deps(body, &predecessors);

        // Second pass: for each statement, find what it reads and link to the
        // most recent write of each read variable.
        for (bi, block) in body.blocks.iter().enumerate() {
            // Track all prior writes within this block as we scan forward.
            let mut local_writes: FxHashMap<usize, FxHashSet<Location>> = FxHashMap::default();

            for (si, stmt) in block.stmts.iter().enumerate() {
                let loc = Location { block: bi, stmt_index: si };
                let reads = stmt_reads(stmt);
                let writes = stmt_writes(stmt);

                // Data deps: for each read, find the last write.
                let mut loc_deps = FxHashSet::default();
                for read_local in &reads {
                    if let Some(write_locs) = local_writes.get(read_local) {
                        loc_deps.extend(write_locs.iter().copied());
                    }
                    if let Some(write_locs) =
                        reaching_defs.get(&bi).and_then(|defs| defs.get(read_local))
                    {
                        loc_deps.extend(write_locs.iter().copied());
                    }
                }

                if let Some(deps) = control_deps.get(&bi) {
                    loc_deps.extend(deps.iter().copied());
                }

                if !loc_deps.is_empty() {
                    deps.insert(loc, loc_deps);
                }

                // Update local writes.
                for write_local in writes {
                    local_writes.entry(write_local).or_default().insert(loc);
                }
            }

            // Terminator deps.
            let term_loc = Location { block: bi, stmt_index: block.stmts.len() };
            let term_reads = terminator_reads(&block.terminator);
            let term_writes = terminator_writes(&block.terminator);

            let mut term_deps = FxHashSet::default();
            for read_local in &term_reads {
                if let Some(write_locs) = local_writes.get(read_local) {
                    term_deps.extend(write_locs.iter().copied());
                }
                if let Some(write_locs) =
                    reaching_defs.get(&bi).and_then(|defs| defs.get(read_local))
                {
                    term_deps.extend(write_locs.iter().copied());
                }
            }

            if let Some(deps) = control_deps.get(&bi) {
                term_deps.extend(deps.iter().copied());
            }

            if !term_deps.is_empty() {
                deps.insert(term_loc, term_deps);
            }

            // Update last-write for terminator writes (e.g., Call destination).
            for write_local in term_writes {
                local_writes.entry(write_local).or_default().insert(term_loc);
            }
        }

        Self { deps, predecessors, num_blocks }
    }

    /// Compute predecessor map: block index -> list of predecessor block indices.
    fn compute_predecessors(body: &VerifiableBody) -> FxHashMap<usize, Vec<usize>> {
        let mut preds: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for (bi, block) in body.blocks.iter().enumerate() {
            for succ in successor_blocks(&block.terminator) {
                preds.entry(succ).or_default().push(bi);
            }
        }
        preds
    }

    /// Compute all writes to each base local in each block.
    fn compute_block_defs(
        body: &VerifiableBody,
    ) -> FxHashMap<usize, FxHashMap<usize, FxHashSet<Location>>> {
        let mut block_defs: FxHashMap<usize, FxHashMap<usize, FxHashSet<Location>>> =
            FxHashMap::default();
        for (bi, block) in body.blocks.iter().enumerate() {
            let mut defs: FxHashMap<usize, FxHashSet<Location>> = FxHashMap::default();
            for (si, stmt) in block.stmts.iter().enumerate() {
                for w in stmt_writes(stmt) {
                    defs.entry(w).or_default().insert(Location { block: bi, stmt_index: si });
                }
            }
            // Include terminator writes.
            for w in terminator_writes(&block.terminator) {
                defs.entry(w)
                    .or_default()
                    .insert(Location { block: bi, stmt_index: block.stmts.len() });
            }
            block_defs.insert(bi, defs);
        }
        block_defs
    }

    fn compute_reaching_defs(
        num_blocks: usize,
        predecessors: &FxHashMap<usize, Vec<usize>>,
        block_defs: &FxHashMap<usize, FxHashMap<usize, FxHashSet<Location>>>,
    ) -> FxHashMap<usize, FxHashMap<usize, FxHashSet<Location>>> {
        let mut reaching: FxHashMap<usize, FxHashMap<usize, FxHashSet<Location>>> =
            FxHashMap::default();
        for block in 0..num_blocks {
            reaching.insert(block, FxHashMap::default());
        }

        let mut changed = true;
        while changed {
            changed = false;
            for block in 0..num_blocks {
                let mut incoming = FxHashMap::default();
                for pred in predecessors.get(&block).into_iter().flatten().copied() {
                    merge_defs(&mut incoming, reaching.get(&pred));
                    merge_defs(&mut incoming, block_defs.get(&pred));
                }
                let entry = reaching.entry(block).or_default();
                let before = entry_len(entry);
                merge_defs(entry, Some(&incoming));
                if entry_len(entry) != before {
                    changed = true;
                }
            }
        }

        reaching
    }

    fn compute_control_deps(
        body: &VerifiableBody,
        predecessors: &FxHashMap<usize, Vec<usize>>,
    ) -> FxHashMap<usize, FxHashSet<Location>> {
        let mut result = FxHashMap::default();
        for block in 0..body.blocks.len() {
            let mut deps = FxHashSet::default();
            let mut seen = FxHashSet::default();
            let mut queue: VecDeque<usize> =
                predecessors.get(&block).cloned().unwrap_or_default().into();
            while let Some(pred) = queue.pop_front() {
                if !seen.insert(pred) {
                    continue;
                }
                let pred_block = &body.blocks[pred];
                if is_conditional_terminator(&pred_block.terminator) {
                    deps.insert(Location { block: pred, stmt_index: pred_block.stmts.len() });
                }
                if let Some(next) = predecessors.get(&pred) {
                    queue.extend(next.iter().copied());
                }
            }
            if !deps.is_empty() {
                result.insert(block, deps);
            }
        }
        result
    }
}

fn merge_defs(
    target: &mut FxHashMap<usize, FxHashSet<Location>>,
    source: Option<&FxHashMap<usize, FxHashSet<Location>>>,
) {
    if let Some(source) = source {
        for (local, defs) in source {
            target.entry(*local).or_default().extend(defs.iter().copied());
        }
    }
}

fn entry_len(entry: &FxHashMap<usize, FxHashSet<Location>>) -> usize {
    entry.values().map(FxHashSet::len).sum()
}

/// Backward slicer: given a target location, computes the transitive closure
/// of dependencies to find all statements that can affect the target.
pub(crate) struct BackwardSlicer<'a> {
    graph: &'a DependencyGraph,
}

impl<'a> BackwardSlicer<'a> {
    pub(crate) fn new(graph: &'a DependencyGraph) -> Self {
        Self { graph }
    }

    /// Compute the backward slice from a target location.
    ///
    /// Returns all locations (statements + terminators) that transitively
    /// affect the target.
    #[must_use]
    pub(crate) fn slice_from(&self, target: Location) -> SliceResult {
        let mut visited = BTreeSet::new();
        let mut worklist = VecDeque::new();

        visited.insert(target);
        worklist.push_back(target);

        while let Some(loc) = worklist.pop_front() {
            if let Some(dep_set) = self.graph.deps.get(&loc) {
                for &dep in dep_set {
                    if visited.insert(dep) {
                        worklist.push_back(dep);
                    }
                }
            }
        }

        SliceResult { locations: visited }
    }
}

/// Compute a backward slice of a VerifiableBody from a target location.
///
/// Returns a SlicedBody where irrelevant statements are replaced with Nop,
/// preserving block structure and terminators.
#[must_use]
pub(crate) fn slice_body(body: &VerifiableBody, target: Location) -> SlicedBody {
    let graph = DependencyGraph::build(body);
    let slicer = BackwardSlicer::new(&graph);
    let mut slice = slicer.slice_from(target);

    let mut sliced = body.clone();
    let mut removed_count = 0;

    for (bi, block) in sliced.blocks.iter_mut().enumerate() {
        for (si, stmt) in block.stmts.iter_mut().enumerate() {
            let loc = Location { block: bi, stmt_index: si };
            if statement_contains_unsupported_mir(stmt) {
                slice.locations.insert(loc);
                continue;
            }
            if !slice.contains(bi, si) && !matches!(stmt, Statement::Nop) {
                *stmt = Statement::Nop;
                removed_count += 1;
            }
        }
    }

    SlicedBody { body: sliced, slice, removed_count }
}

fn statement_contains_unsupported_mir(stmt: &Statement) -> bool {
    match stmt {
        Statement::Unsupported { .. } => true,
        Statement::Assign { rvalue, .. } => rvalue_contains_unsupported_mir(rvalue),
        Statement::Intrinsic { args, .. } => args.iter().any(operand_contains_unsupported_mir),
        _ => false,
    }
}

fn rvalue_contains_unsupported_mir(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Unsupported { .. } => true,
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            operand_contains_unsupported_mir(op)
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_contains_unsupported_mir(lhs) || operand_contains_unsupported_mir(rhs)
        }
        Rvalue::Aggregate(_, operands) => operands.iter().any(operand_contains_unsupported_mir),
        _ => false,
    }
}

fn operand_contains_unsupported_mir(operand: &Operand) -> bool {
    matches!(operand, Operand::Unsupported { .. })
}

// --- Helper functions for extracting reads/writes from statements ---

/// Extract the set of local variable indices read by a statement.
fn stmt_reads(stmt: &Statement) -> Vec<usize> {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            let mut reads = place_reads(place);
            reads.extend(rvalue_reads(rvalue));
            reads
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => place_reads(place),
        Statement::Intrinsic { args, .. } | Statement::Unsupported { operands: args, .. } => {
            args.iter().flat_map(operand_reads).collect()
        }
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => vec![],
        _ => vec![],
    }
}

/// Extract the set of local variable indices written by a statement.
fn stmt_writes(stmt: &Statement) -> Vec<usize> {
    match stmt {
        Statement::Assign { place, .. } => vec![place.local],
        Statement::StorageLive(local) | Statement::StorageDead(local) => vec![*local],
        Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
            vec![place.local]
        }
        Statement::Retag { place } => vec![place.local],
        Statement::PlaceMention(_)
        | Statement::Intrinsic { .. }
        | Statement::Unsupported { .. }
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => vec![],
        _ => vec![],
    }
}

fn place_reads(place: &Place) -> Vec<usize> {
    let mut reads = vec![place.local];
    for projection in &place.projections {
        if let Projection::Index(index) = projection {
            reads.push(*index);
        }
    }
    reads
}

/// Extract local variable indices read by an rvalue.
fn rvalue_reads(rvalue: &Rvalue) -> Vec<usize> {
    match rvalue {
        Rvalue::Use(op) => operand_reads(op),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            let mut reads = operand_reads(lhs);
            reads.extend(operand_reads(rhs));
            reads
        }
        Rvalue::UnaryOp(_, op) => operand_reads(op),
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => place_reads(place),
        Rvalue::Cast(op, _) => operand_reads(op),
        Rvalue::Aggregate(_, ops) => ops.iter().flat_map(operand_reads).collect(),
        Rvalue::Discriminant(place) | Rvalue::Len(place) | Rvalue::CopyForDeref(place) => {
            place_reads(place)
        }
        Rvalue::Repeat(op, _) => operand_reads(op),
        Rvalue::Unsupported { operands, .. } => operands.iter().flat_map(operand_reads).collect(),
        _ => vec![],
    }
}

/// Extract local variable indices read by an operand.
fn operand_reads(operand: &Operand) -> Vec<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_reads(place),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => vec![],
        _ => vec![],
    }
}

/// Extract local variable indices read by a terminator.
fn terminator_reads(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::SwitchInt { discr, .. } => operand_reads(discr),
        Terminator::Assert { cond, .. } => operand_reads(cond),
        Terminator::Call { args, .. } => args.iter().flat_map(operand_reads).collect(),
        Terminator::Drop { place, .. } => place_reads(place),
        Terminator::Goto(_)
        | Terminator::Opaque { .. }
        | Terminator::Return
        | Terminator::Unreachable => vec![],
        _ => vec![],
    }
}

/// Extract local variable indices written by a terminator.
fn terminator_writes(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Call { dest, .. } => vec![dest.local],
        _ => vec![],
    }
}

/// Get successor block indices from a terminator.
fn successor_blocks(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Goto(BlockId(b)) => vec![*b],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<usize> = targets.iter().map(|(_, BlockId(b))| *b).collect();
            succs.push(otherwise.0);
            succs
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().map(|BlockId(b)| *b).collect(),
        Terminator::Assert { target: BlockId(b), .. } => vec![*b],
        Terminator::Drop { target: BlockId(b), .. } => vec![*b],
        Terminator::Opaque { targets, .. } => targets.iter().map(|BlockId(b)| *b).collect(),
        _ => vec![],
    }
}

/// Returns true if a terminator is conditional (introduces control flow choice).
fn is_conditional_terminator(term: &Terminator) -> bool {
    matches!(term, Terminator::SwitchInt { .. } | Terminator::Assert { .. })
        || matches!(term, Terminator::Opaque { targets, .. } if targets.len() > 1)
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    /// Build a 10-statement function where backward slicing from the return
    /// value reduces to only 3 relevant statements.
    ///
    /// Function logic (pseudocode):
    ///   _1: i32 (arg x)
    ///   _2: i32 (arg y)
    ///   _3 = _1 + _2          // stmt 0: relevant (feeds _5)
    ///   _4 = _1 * _1          // stmt 1: irrelevant (dead)
    ///   _5 = _3 + 1           // stmt 2: relevant (feeds _0)
    ///   _6 = _2 - _1          // stmt 3: irrelevant (dead)
    ///   _7 = _4 + _6          // stmt 4: irrelevant (dead, reads dead _4 and _6)
    ///   _8 = _7 + 10          // stmt 5: irrelevant (dead)
    ///   _9 = _1 + _2          // stmt 6: irrelevant (duplicate, dead)
    ///   _10 = _8 + _9         // stmt 7: irrelevant (dead)
    ///   _11 = _5 + 0          // stmt 8: irrelevant (dead, reads _5 but not used by target)
    ///   _0 = _5               // stmt 9: target (return value assignment)
    ///
    /// Backward slice from stmt 9 (_0 = _5):
    ///   - stmt 9: _0 = _5 (target, reads _5)
    ///   - stmt 2: _5 = _3 + 1 (writes _5, reads _3)
    ///   - stmt 0: _3 = _1 + _2 (writes _3, reads _1, _2 which are args)
    ///   Total: 3 statements in slice.
    fn build_ten_stmt_body() -> VerifiableBody {
        let span = SourceSpan::default();
        VerifiableBody {
            locals: (0..12).map(|i| LocalDecl { index: i, ty: Ty::i32(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // stmt 0: _3 = _1 + _2
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 1: _4 = _1 * _1
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 2: _5 = _3 + 1
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 3: _6 = _2 - _1
                    Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 4: _7 = _4 + _6
                    Statement::Assign {
                        place: Place::local(7),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(4)),
                            Operand::Copy(Place::local(6)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 5: _8 = _7 + 10
                    Statement::Assign {
                        place: Place::local(8),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(7)),
                            Operand::Constant(ConstValue::Int(10)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 6: _9 = _1 + _2
                    Statement::Assign {
                        place: Place::local(9),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 7: _10 = _8 + _9
                    Statement::Assign {
                        place: Place::local(10),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(8)),
                            Operand::Copy(Place::local(9)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 8: _11 = _5 + 0 (reads _5, but result is dead)
                    Statement::Assign {
                        place: Place::local(11),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(5)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span.clone(),
                    },
                    // stmt 9: _0 = _5
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        }
    }

    #[test]
    fn test_backward_slice_ten_stmts_reduces_to_three() {
        let body = build_ten_stmt_body();
        let target = Location { block: 0, stmt_index: 9 }; // _0 = _5

        let graph = DependencyGraph::build(&body);
        let slicer = BackwardSlicer::new(&graph);
        let result = slicer.slice_from(target);

        // Slice should contain exactly: stmt 0, stmt 2, stmt 9
        assert!(result.contains(0, 9), "target stmt 9 must be in slice");
        assert!(result.contains(0, 2), "stmt 2 (_5 = _3 + 1) must be in slice");
        assert!(result.contains(0, 0), "stmt 0 (_3 = _1 + _2) must be in slice");

        assert_eq!(result.len(), 3, "slice should have exactly 3 statements");

        // Verify irrelevant statements are NOT in slice
        assert!(!result.contains(0, 1), "stmt 1 (_4 = _1*_1) should NOT be in slice");
        assert!(!result.contains(0, 3), "stmt 3 (_6 = _2-_1) should NOT be in slice");
        assert!(!result.contains(0, 4), "stmt 4 (_7 = _4+_6) should NOT be in slice");
        assert!(!result.contains(0, 5), "stmt 5 (_8 = _7+10) should NOT be in slice");
        assert!(!result.contains(0, 6), "stmt 6 (_9 = _1+_2) should NOT be in slice");
        assert!(!result.contains(0, 7), "stmt 7 (_10 = _8+_9) should NOT be in slice");
        assert!(!result.contains(0, 8), "stmt 8 (_11 = _5+0) should NOT be in slice");
    }

    #[test]
    fn test_slice_body_replaces_irrelevant_with_nop() {
        let body = build_ten_stmt_body();
        let target = Location { block: 0, stmt_index: 9 };

        let sliced = slice_body(&body, target);

        // 7 irrelevant statements should become Nop
        assert_eq!(sliced.removed_count, 7);

        let stmts = &sliced.body.blocks[0].stmts;
        assert!(matches!(stmts[0], Statement::Assign { .. }), "stmt 0 kept");
        assert!(matches!(stmts[1], Statement::Nop), "stmt 1 replaced");
        assert!(matches!(stmts[2], Statement::Assign { .. }), "stmt 2 kept");
        assert!(matches!(stmts[3], Statement::Nop), "stmt 3 replaced");
        assert!(matches!(stmts[4], Statement::Nop), "stmt 4 replaced");
        assert!(matches!(stmts[5], Statement::Nop), "stmt 5 replaced");
        assert!(matches!(stmts[6], Statement::Nop), "stmt 6 replaced");
        assert!(matches!(stmts[7], Statement::Nop), "stmt 7 replaced");
        assert!(matches!(stmts[8], Statement::Nop), "stmt 8 replaced");
        assert!(matches!(stmts[9], Statement::Assign { .. }), "stmt 9 kept");
    }

    fn unsupported_slice_body(stmt0: Statement) -> VerifiableBody {
        let span = SourceSpan::default();
        VerifiableBody {
            locals: (0..3).map(|i| LocalDecl { index: i, ty: Ty::i32(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    stmt0,
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span,
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        }
    }

    fn assert_dead_unsupported_stmt_is_preserved(stmt0: Statement) {
        let body = unsupported_slice_body(stmt0);
        let sliced = slice_body(&body, Location { block: 0, stmt_index: 2 });
        let stmts = &sliced.body.blocks[0].stmts;

        assert!(sliced.slice.contains(0, 0), "unsupported-bearing stmt must be in slice metadata");
        assert!(!matches!(stmts[0], Statement::Nop), "unsupported-bearing stmt must be kept");
        assert!(matches!(stmts[1], Statement::Nop), "ordinary dead stmt should still be removed");
        assert!(matches!(stmts[2], Statement::Assign { .. }), "target stmt kept");
    }

    #[test]
    fn test_slice_body_preserves_dead_statement_unsupported() {
        assert_dead_unsupported_stmt_is_preserved(Statement::Unsupported {
            kind: "StatementKind::Intrinsic".to_string(),
            detail: "copy_nonoverlapping".to_string(),
            operands: vec![],
            span: SourceSpan::default(),
        });
    }

    #[test]
    fn test_slice_body_preserves_dead_rvalue_unsupported() {
        assert_dead_unsupported_stmt_is_preserved(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Unsupported {
                kind: "Rvalue::ThreadLocalRef".to_string(),
                detail: "TLS read".to_string(),
                operands: vec![],
            },
            span: SourceSpan::default(),
        });
    }

    #[test]
    fn test_slice_body_preserves_dead_operand_unsupported() {
        assert_dead_unsupported_stmt_is_preserved(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Unsupported {
                kind: "ConstValue::Ty".to_string(),
                detail: "unsupported constant".to_string(),
            }),
            span: SourceSpan::default(),
        });
    }

    #[test]
    fn test_slice_with_control_dependency() {
        // Two blocks: bb0 has a conditional branch, bb1 has the target.
        // Statements in bb1 should have a control dep on bb0's terminator.
        //
        // bb0:
        //   _3 = _1 + _2      (stmt 0)
        //   SwitchInt(_1) -> [0: bb1], otherwise: bb2
        //
        // bb1:
        //   _0 = _3            (stmt 0, target)
        //   Return
        //
        // bb2:
        //   _0 = const 0       (stmt 0)
        //   Return
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: (0..4).map(|i| LocalDecl { index: i, ty: Ty::i32(), name: None }).collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        };

        // Slice from bb1, stmt 0 (_0 = _3)
        let target = Location { block: 1, stmt_index: 0 };
        let graph = DependencyGraph::build(&body);
        let slicer = BackwardSlicer::new(&graph);
        let result = slicer.slice_from(target);

        // Should include:
        // - bb1 stmt 0 (target, reads _3)
        // - bb0 stmt 0 (_3 = _1 + _2, writes _3)
        // - bb0 terminator (control dep, since bb1 is reachable only via SwitchInt)
        assert!(result.contains(1, 0), "target must be in slice");
        assert!(result.contains(0, 0), "bb0 stmt 0 must be in slice (data dep on _3)");
        assert!(result.contains(0, 1), "bb0 terminator (index 1) must be in slice (control dep)");

        // bb2 stmt 0 should NOT be in slice
        assert!(!result.contains(2, 0), "bb2 stmt 0 should not be in slice");
    }

    #[test]
    fn test_empty_slice_for_constant_target() {
        // Single block: _0 = const 42. Slice from that stmt.
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let target = Location { block: 0, stmt_index: 0 };
        let result = slice_body(&body, target);

        // Only the target itself, no dependencies.
        assert_eq!(result.slice.len(), 1);
        assert_eq!(result.removed_count, 0);
    }

    #[test]
    fn test_slice_result_is_empty() {
        let result = SliceResult { locations: BTreeSet::new() };
        assert!(result.is_empty());
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_dependency_graph_predecessors() {
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span,
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let graph = DependencyGraph::build(&body);
        assert_eq!(graph.predecessors.get(&1).unwrap(), &vec![0usize]);
        assert!(graph.predecessors.get(&0).is_none());
    }

    #[test]
    fn test_slice_through_call_terminator() {
        // bb0: Call { func: "f", args: [_1], dest: _2, target: Some(bb1) }
        // bb1: _0 = _2; Return
        //
        // Slice from bb1 stmt 0 should include bb0 terminator (writes _2).
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: (0..3).map(|i| LocalDecl { index: i, ty: Ty::i32(), name: None }).collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "f".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span,
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        };

        let target = Location { block: 1, stmt_index: 0 };
        let graph = DependencyGraph::build(&body);
        let slicer = BackwardSlicer::new(&graph);
        let result = slicer.slice_from(target);

        // bb1 stmt 0 (target) + bb0 terminator (writes _2)
        assert!(result.contains(1, 0), "target in slice");
        assert!(result.contains(0, 0), "bb0 terminator (Call writes _2) in slice");
        assert_eq!(result.len(), 2);
    }

    // Trust: #472 — Additional slicing tests for test density improvement

    // --- stmt_reads / stmt_writes tests ---

    #[test]
    fn test_stmt_reads_assign_binary_op() {
        let stmt = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        };
        let reads = stmt_reads(&stmt);
        assert!(reads.contains(&1));
        assert!(reads.contains(&2));
    }

    #[test]
    fn test_stmt_reads_nop() {
        assert!(stmt_reads(&Statement::Nop).is_empty());
    }

    #[test]
    fn test_stmt_writes_assign() {
        let stmt = Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: SourceSpan::default(),
        };
        let writes = stmt_writes(&stmt);
        assert_eq!(writes, vec![5]);
    }

    #[test]
    fn test_stmt_writes_nop() {
        assert!(stmt_writes(&Statement::Nop).is_empty());
    }

    // --- rvalue_reads tests ---

    #[test]
    fn test_rvalue_reads_use_copy() {
        let reads = rvalue_reads(&Rvalue::Use(Operand::Copy(Place::local(3))));
        assert_eq!(reads, vec![3]);
    }

    #[test]
    fn test_rvalue_reads_use_move() {
        let reads = rvalue_reads(&Rvalue::Use(Operand::Move(Place::local(7))));
        assert_eq!(reads, vec![7]);
    }

    #[test]
    fn test_rvalue_reads_use_constant() {
        let reads = rvalue_reads(&Rvalue::Use(Operand::Constant(ConstValue::Int(0))));
        assert!(reads.is_empty());
    }

    #[test]
    fn test_rvalue_reads_checked_binary_op() {
        let reads = rvalue_reads(&Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Move(Place::local(2)),
        ));
        assert!(reads.contains(&1));
        assert!(reads.contains(&2));
    }

    #[test]
    fn test_rvalue_reads_unary_op() {
        let reads = rvalue_reads(&Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(4))));
        assert_eq!(reads, vec![4]);
    }

    #[test]
    fn test_rvalue_reads_ref() {
        let reads = rvalue_reads(&Rvalue::Ref { mutable: false, place: Place::local(10) });
        assert_eq!(reads, vec![10]);
    }

    #[test]
    fn test_rvalue_reads_address_of() {
        let reads = rvalue_reads(&Rvalue::AddressOf(true, Place::local(8)));
        assert_eq!(reads, vec![8]);
    }

    #[test]
    fn test_rvalue_reads_cast() {
        let reads = rvalue_reads(&Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::i64()));
        assert_eq!(reads, vec![2]);
    }

    #[test]
    fn test_rvalue_reads_aggregate() {
        let reads = rvalue_reads(&Rvalue::Aggregate(
            AggregateKind::Tuple,
            vec![
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(3)),
                Operand::Constant(ConstValue::Int(0)),
            ],
        ));
        assert!(reads.contains(&1));
        assert!(reads.contains(&3));
        assert_eq!(reads.len(), 2);
    }

    #[test]
    fn test_rvalue_reads_discriminant() {
        let reads = rvalue_reads(&Rvalue::Discriminant(Place::local(5)));
        assert_eq!(reads, vec![5]);
    }

    #[test]
    fn test_rvalue_reads_len() {
        let reads = rvalue_reads(&Rvalue::Len(Place::local(6)));
        assert_eq!(reads, vec![6]);
    }

    #[test]
    fn test_rvalue_reads_repeat() {
        let reads = rvalue_reads(&Rvalue::Repeat(Operand::Copy(Place::local(2)), 10));
        assert_eq!(reads, vec![2]);
    }

    #[test]
    fn test_rvalue_reads_copy_for_deref() {
        let reads = rvalue_reads(&Rvalue::CopyForDeref(Place::local(9)));
        assert_eq!(reads, vec![9]);
    }

    // --- operand_reads with projections ---

    #[test]
    fn test_operand_reads_index_projection() {
        let place = Place { local: 5, projections: vec![Projection::Index(3)] };
        let reads = operand_reads(&Operand::Copy(place));
        assert!(reads.contains(&5), "should read base local");
        assert!(reads.contains(&3), "should read index local");
    }

    #[test]
    fn test_operand_reads_field_projection_no_extra_read() {
        let place = Place { local: 5, projections: vec![Projection::Field(2)] };
        let reads = operand_reads(&Operand::Copy(place));
        assert_eq!(reads, vec![5], "Field projection does not add a read");
    }

    #[test]
    fn test_operand_reads_deref_projection_no_extra_read() {
        let place = Place { local: 5, projections: vec![Projection::Deref] };
        let reads = operand_reads(&Operand::Copy(place));
        assert_eq!(reads, vec![5], "Deref projection does not add a read");
    }

    // --- terminator_reads / terminator_writes tests ---

    #[test]
    fn test_terminator_reads_switch_int() {
        let term = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets: vec![(0, BlockId(2))],
            otherwise: BlockId(3),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        let reads = terminator_reads(&term);
        assert_eq!(reads, vec![1]);
    }

    #[test]
    fn test_terminator_reads_assert() {
        let term = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Copy(Place::local(4)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(1),
            span: SourceSpan::default(),
        };
        let reads = terminator_reads(&term);
        assert_eq!(reads, vec![4]);
    }

    #[test]
    fn test_terminator_reads_call() {
        let term = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "foo".to_string(),
            args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(2))],
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
        };
        let reads = terminator_reads(&term);
        assert!(reads.contains(&1));
        assert!(reads.contains(&2));
    }

    #[test]
    fn test_terminator_reads_drop() {
        let term = Terminator::Drop {
            unwind: UnwindEdge::Unreachable,
            place: Place::local(3),
            target: BlockId(1),
            span: SourceSpan::default(),
        };
        let reads = terminator_reads(&term);
        assert_eq!(reads, vec![3]);
    }

    #[test]
    fn test_terminator_reads_goto_return_unreachable() {
        assert!(terminator_reads(&Terminator::Goto(BlockId(1))).is_empty());
        assert!(terminator_reads(&Terminator::Return).is_empty());
        assert!(terminator_reads(&Terminator::Unreachable).is_empty());
    }

    #[test]
    fn test_terminator_writes_call_dest() {
        let term = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "f".to_string(),
            args: vec![],
            dest: Place::local(5),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
        };
        let writes = terminator_writes(&term);
        assert_eq!(writes, vec![5]);
    }

    #[test]
    fn test_terminator_writes_non_call_empty() {
        assert!(terminator_writes(&Terminator::Return).is_empty());
        assert!(terminator_writes(&Terminator::Goto(BlockId(0))).is_empty());
        assert!(terminator_writes(&Terminator::Unreachable).is_empty());
    }

    // --- successor_blocks tests ---

    #[test]
    fn test_successor_blocks_goto() {
        assert_eq!(successor_blocks(&Terminator::Goto(BlockId(5))), vec![5]);
    }

    #[test]
    fn test_successor_blocks_switch_int() {
        let term = Terminator::SwitchInt {
            discr: Operand::Constant(ConstValue::Int(0)),
            targets: vec![(0, BlockId(1)), (1, BlockId(2))],
            otherwise: BlockId(3),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        let succs = successor_blocks(&term);
        assert_eq!(succs, vec![1, 2, 3]);
    }

    #[test]
    fn test_successor_blocks_return_unreachable() {
        assert!(successor_blocks(&Terminator::Return).is_empty());
        assert!(successor_blocks(&Terminator::Unreachable).is_empty());
    }

    #[test]
    fn test_successor_blocks_call_with_target() {
        let term = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "f".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: Some(BlockId(4)),
            span: SourceSpan::default(),
            atomic: None,
        };
        assert_eq!(successor_blocks(&term), vec![4]);
    }

    #[test]
    fn test_successor_blocks_call_no_target() {
        let term = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "f".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
        };
        assert!(successor_blocks(&term).is_empty());
    }

    #[test]
    fn test_successor_blocks_assert() {
        let term = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(2),
            span: SourceSpan::default(),
        };
        assert_eq!(successor_blocks(&term), vec![2]);
    }

    #[test]
    fn test_successor_blocks_drop() {
        let term = Terminator::Drop {
            unwind: UnwindEdge::Unreachable,
            place: Place::local(1),
            target: BlockId(3),
            span: SourceSpan::default(),
        };
        assert_eq!(successor_blocks(&term), vec![3]);
    }

    // --- is_conditional_terminator tests ---

    #[test]
    fn test_is_conditional_terminator_switch_int() {
        let term = Terminator::SwitchInt {
            discr: Operand::Constant(ConstValue::Int(0)),
            targets: vec![],
            otherwise: BlockId(0),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        assert!(is_conditional_terminator(&term));
    }

    #[test]
    fn test_is_conditional_terminator_assert() {
        let term = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(0),
            span: SourceSpan::default(),
        };
        assert!(is_conditional_terminator(&term));
    }

    #[test]
    fn test_is_conditional_terminator_non_conditional() {
        assert!(!is_conditional_terminator(&Terminator::Goto(BlockId(0))));
        assert!(!is_conditional_terminator(&Terminator::Return));
        assert!(!is_conditional_terminator(&Terminator::Unreachable));
    }

    // --- Slice edge cases ---

    #[test]
    fn test_slice_empty_body() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        // Slice from the terminator location
        let target = Location { block: 0, stmt_index: 0 };
        let result = slice_body(&body, target);
        assert_eq!(result.removed_count, 0);
        assert_eq!(result.slice.len(), 1);
    }

    #[test]
    fn test_slice_chain_dependency() {
        // _1 = 10, _2 = _1 + 1, _3 = _2 + 1, target: _0 = _3
        // All should be in slice (transitive chain)
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: (0..4).map(|i| LocalDecl { index: i, ty: Ty::i32(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span,
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let target = Location { block: 0, stmt_index: 3 };
        let result = slice_body(&body, target);
        assert_eq!(result.slice.len(), 4, "all 4 stmts form a dependency chain");
        assert_eq!(result.removed_count, 0);
    }

    #[test]
    fn test_slice_diamond_control_flow() {
        // bb0: SwitchInt(_1) -> [0: bb1], otherwise: bb2
        // bb1: _2 = 10; goto bb3
        // bb2: _2 = 20; goto bb3
        // bb3: _0 = _2; return
        //
        // Slice from bb3 stmt 0 should include control deps.
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: (0..3).map(|i| LocalDecl { index: i, ty: Ty::i32(), name: None }).collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span,
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        };

        let target = Location { block: 3, stmt_index: 0 };
        let graph = DependencyGraph::build(&body);
        let slicer = BackwardSlicer::new(&graph);
        let result = slicer.slice_from(target);

        // Target (bb3:0) is in slice
        assert!(result.contains(3, 0), "target must be in slice");
        // Both assignments to _2 should be in slice (bb1:0 and bb2:0)
        assert!(
            result.contains(1, 0) || result.contains(2, 0),
            "at least one assignment to _2 should be in slice"
        );
    }

    #[test]
    fn test_slice_result_contains_and_len() {
        let mut locs = BTreeSet::new();
        locs.insert(Location { block: 0, stmt_index: 0 });
        locs.insert(Location { block: 1, stmt_index: 2 });
        locs.insert(Location { block: 2, stmt_index: 5 });

        let result = SliceResult { locations: locs };
        assert_eq!(result.len(), 3);
        assert!(!result.is_empty());
        assert!(result.contains(0, 0));
        assert!(result.contains(1, 2));
        assert!(result.contains(2, 5));
        assert!(!result.contains(0, 1));
        assert!(!result.contains(3, 0));
    }

    #[test]
    fn test_location_ordering() {
        let a = Location { block: 0, stmt_index: 1 };
        let b = Location { block: 0, stmt_index: 2 };
        let c = Location { block: 1, stmt_index: 0 };
        assert!(a < b);
        assert!(b < c);
        assert!(a < c);
    }

    #[test]
    fn test_dependency_graph_multi_block_predecessors() {
        // bb0 -> bb2, bb1 -> bb2: bb2 has two predecessors
        let span = SourceSpan::default();
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span,
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let graph = DependencyGraph::build(&body);
        let preds = graph.predecessors.get(&2).unwrap();
        assert!(preds.contains(&0));
        assert!(preds.contains(&1));
        assert_eq!(preds.len(), 2);
    }
}
