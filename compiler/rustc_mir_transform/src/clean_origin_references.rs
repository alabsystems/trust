//! Demand native Clean gates for actual Rust references, including check-only builds.
//!
//! The direct-IR selector is an additional artifact check: it cannot supply this
//! inventory when IR lowering is disabled. Retain only typed source identities
//! from executable MIR operands. Local/debug types alone do not reference code.

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Body, ConstOperand, Location, Operand};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::LocalDefId;

use crate::clean_origin_mir::is_clean_origin;

struct References<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    referenced: FxHashSet<LocalDefId>,
}

impl<'tcx> References<'_, 'tcx> {
    fn record(&mut self, ty: Ty<'tcx>) {
        if let ty::FnDef(def, _) = ty.kind()
            && let Some(local) = def.as_local()
            && is_clean_origin(self.tcx, local)
        {
            self.referenced.insert(local);
        }
    }
}

impl<'tcx> Visitor<'tcx> for References<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        // Calls and function-address reifications can use Constant, Copy or Move.
        // Inspect their exact function-item type, without normalization or CTFE.
        // Constant operands are recorded by `visit_const_operand` via `super_operand`.
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty = if place.projection.is_empty() {
                    self.body.local_decls[place.local].ty
                } else {
                    place.ty(&self.body.local_decls, self.tcx).ty
                };
                self.record(ty);
            }
            Operand::Constant(_) | Operand::RuntimeChecks(_) => {}
        }
        self.super_operand(operand, location);
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _: Location) {
        // Inline/global assembly `sym fn` reaches this visitor directly.
        self.record(constant.const_.ty());
    }
}

/// Provider for a disk-cached, pre-steal reference inventory.
pub(crate) fn references<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> &'tcx [LocalDefId] {
    if tcx.resolutions(()).clean_origin_defs.is_empty() {
        return &[];
    }
    // `mir_promoted` ensures this query before the sole raw-MIR steal. Do not
    // inspect `is_stolen` or substitute an empty result based on query order.
    let body = tcx.mir_built(owner).borrow();
    let mut visitor = References { tcx, body: &body, referenced: FxHashSet::default() };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        visitor.visit_basic_block_data(block, data);
    }
    if visitor.referenced.is_empty() {
        return &[];
    }
    let mut referenced: Vec<_> = visitor.referenced.into_iter().collect();
    referenced.sort_unstable_by_key(|def| def.local_def_index.as_u32());
    tcx.arena.alloc_from_iter(referenced)
}

/// Run after successful frontend analysis and the pre-steal Trust initializers.
/// This only demands existing native gates; it creates no IR or proof authority.
///
/// Trust (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.1): not on F1
/// with the trust-ir producer running (`clean_origin_ir::records_on_f1`). There the Clean recorder
/// runs on every compile, verification on or off, and the language's call gate for a Rust callee
/// is decided on trust-ir after the finalize (`clean_origin_ir::check_rust_callees_on_f1`), which
/// falls back to [`demand_referenced`] when no module was published. On every other lane, as
/// before.
pub fn ensure_referenced(tcx: TyCtxt<'_>) {
    if crate::clean_origin_ir::records_on_f1(tcx) {
        return;
    }
    demand_referenced(tcx);
}

/// Demand the native gate (the `clean_origin_mir` body) of every Clean-origin def this crate's
/// Rust MIR references; each demand is charged to the reach counter's `recorder` lane.
pub(crate) fn demand_referenced(tcx: TyCtxt<'_>) {
    if tcx.resolutions(()).clean_origin_defs.is_empty() {
        return;
    }
    let mut referenced = FxHashSet::default();
    // Include constants, statics, custom MIR and global assembly as well as
    // ordinary functions. A successful empty result is distinct from not running
    // the query; no producer-lowering outcome can reduce this population.
    for owner in tcx.hir_body_owners() {
        referenced.extend(tcx.trust_clean_origin_references(owner).iter().copied());
    }
    let mut referenced: Vec<_> = referenced.into_iter().collect();
    referenced.sort_unstable_by_key(|def| def.local_def_index.as_u32());
    for def in referenced {
        let _ask = crate::clean_origin_ir::clean_origin_reach::ask(
            tcx.sess,
            crate::clean_origin_ir::clean_origin_reach::ReachLane::Recorder,
        );
        let _ = tcx.optimized_mir(def.to_def_id());
    }
}
