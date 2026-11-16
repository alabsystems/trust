//! Store-only reaching copies of entry argument values.
//!
//! This is independent of `MirRoots`: it cannot authorize call equivalence or
//! decide that a store is private. Every fact is a whole-local copy, never a
//! pointee alias, validity, borrowing, or disjointness assertion.

use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    Body, Local, Location, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
    StatementKind, TerminatorKind,
};

#[path = "store_root_facts/core.rs"]
mod core;
use core::{Block, Facts, Program, Step};

pub(super) struct StoreRootFacts {
    facts: Facts,
    locations: Vec<Vec<usize>>,
}

fn has_deref(place: &Place<'_>) -> bool {
    place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
}

fn whole_operand(operand: &Operand<'_>) -> Option<usize> {
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local.as_usize()),
        _ => None,
    }
}

#[derive(Default)]
struct Moves(Vec<usize>);
impl<'tcx> Visitor<'tcx> for Moves {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        if let Operand::Move(p) = operand {
            // Moving a field invalidates the whole containing local. Moving
            // through a pointer changes its pointee, not the pointer local.
            if !has_deref(p) {
                self.0.push(p.local.as_usize());
            }
        }
        self.super_operand(operand, location);
    }
}

struct Exposed(Vec<bool>);
impl<'tcx> Visitor<'tcx> for Exposed {
    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p) | Rvalue::Reborrow(_, _, p) = value {
            // &raw mut p exposes p's storage; &raw mut *p exposes the pointee.
            // A globally exposed local is unknown even before the exposure,
            // avoiding any assumption about alias lifetime or call effects.
            if !has_deref(p) {
                if let Some(slot) = self.0.get_mut(p.local.as_usize()) {
                    *slot = true;
                }
            }
        }
        self.super_rvalue(value, location);
    }
}

fn kill_definition(place: &Place<'_>, steps: &mut Vec<Step>) {
    if !has_deref(place) {
        steps.push(Step::Kill(vec![place.local.as_usize()]));
    }
}

impl StoreRootFacts {
    /// `successors` is the existing conservation census's real normal-path CFG:
    /// false/cleanup edges and inhabited-return decisions are not recomputed.
    pub(super) fn compute(
        body: &Body<'_>,
        reachable: &[bool],
        successors: Vec<Vec<usize>>,
    ) -> Self {
        Self::for_cfg(body, body.local_decls.len(), reachable, successors)
    }

    fn for_cfg(
        body: &Body<'_>,
        locals: usize,
        reachable: &[bool],
        successors: Vec<Vec<usize>>,
    ) -> Self {
        let mut exposed = Exposed(vec![false; locals]);
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if reachable.get(bb.as_usize()) == Some(&true) {
                exposed.visit_basic_block_data(bb, data);
            }
        }
        let mut blocks = Vec::new();
        let mut locations = Vec::new();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let mut steps = Vec::new();
            let mut points = Vec::new();
            for (statement_index, stmt) in data.statements.iter().enumerate() {
                let location = Location { block: bb, statement_index };
                points.push(steps.len());
                steps.push(Step::Observe);
                let mut moves = Moves::default();
                moves.visit_statement(stmt, location);
                match &stmt.kind {
                    StatementKind::Assign(assign) => {
                        let (dest, value) = &**assign;
                        if dest.projection.is_empty() {
                            let src = match value {
                                Rvalue::Use(op, _) => whole_operand(op),
                                Rvalue::CopyForDeref(p) if p.projection.is_empty() => {
                                    Some(p.local.as_usize())
                                }
                                _ => None,
                            };
                            steps.push(Step::Assign {
                                dst: dest.local.as_usize(),
                                src,
                                moved: moves.0,
                            });
                        } else {
                            steps.push(Step::Kill(moves.0));
                            kill_definition(dest, &mut steps);
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        kill_definition(place, &mut steps);
                    }
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                        steps.push(Step::Kill(vec![local.as_usize()]));
                    }
                    // No other statement can assign a pointer local. Intrinsic
                    // writes access pointees; escaped local storage was banned.
                    StatementKind::Intrinsic(_) => steps.push(Step::Kill(moves.0)),
                    StatementKind::FakeRead(_)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType(_, _)
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop
                    | StatementKind::BackwardIncompatibleDropHint { .. } => {}
                }
            }
            let location = Location { block: bb, statement_index: data.statements.len() };
            if let Some(term) = &data.terminator {
                let mut moves = Moves::default();
                moves.visit_terminator(term, location);
                // A call's returned store occurs after its argument moves. No
                // return value is ever assumed to copy a particular argument.
                steps.push(Step::Kill(moves.0));
                points.push(steps.len());
                steps.push(Step::Observe);
                match &term.kind {
                    TerminatorKind::Call { destination, .. } => {
                        kill_definition(destination, &mut steps);
                    }
                    TerminatorKind::Drop { place, .. } => kill_definition(place, &mut steps),
                    TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => {
                        steps.push(Step::KillAll);
                    }
                    _ => {}
                }
            } else {
                points.push(steps.len());
                steps.push(Step::Observe);
            }
            let next = if reachable.get(bb.as_usize()) == Some(&true) {
                successors.get(bb.as_usize()).cloned().unwrap_or_default()
            } else {
                Vec::new()
            };
            blocks.push(Block { steps, successors: next });
            locations.push(points);
        }
        let facts = core::analyze(&Program {
            locals,
            arguments: body.args_iter().map(Local::as_usize).collect(),
            exposed: exposed.0,
            blocks,
        });
        Self { facts, locations }
    }

    fn argument_at(&self, location: Location, local: Local) -> Option<u32> {
        let block = location.block.as_usize();
        let step = *self.locations.get(block)?.get(location.statement_index)?;
        self.facts.at(block, step, local.as_usize())
    }

    /// Exactly one leading dereference: suffix fields/indices change the
    /// address within the same argument root; a loaded pointer never qualifies.
    pub(super) fn store_argument(&self, location: Location, place: &Place<'_>) -> Option<u32> {
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref))
            || place.projection[1..].iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return None;
        }
        self.argument_at(location, place.local)
    }

    pub(super) fn copy_destination_argument(
        &self,
        location: Location,
        intrinsic: &NonDivergingIntrinsic<'_>,
    ) -> Option<u32> {
        let NonDivergingIntrinsic::CopyNonOverlapping(copy) = intrinsic else { return None };
        let local = whole_operand(&copy.dst)?;
        self.argument_at(location, Local::from_usize(local))
    }
}

#[cfg(test)]
#[path = "store_root_facts/tests.rs"]
mod tests;
