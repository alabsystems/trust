use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{self, Location, MentionedItem};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Span, Spanned};

use crate::PassPolicy;

pub(super) struct MentionedItems;

// Trust: the visitor reports each item to a callback with its location, so the spawn
// census (design 2026-09-29-spawn-census-by-construction §5.1) enumerates a pre-steal
// body exactly as this pass enumerates the codegen body. Reverted at the census flip.
struct MentionedItemsVisitor<'a, 'tcx, F> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    mentioned_item: F,
}

/// Trust: every item this pass would record for `body`, in the same order, each with
/// the location that mentions it (spawn census, `trust_verify::trust_spawn_census`).
pub(crate) fn for_each_mentioned_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    mentioned_item: impl FnMut(MentionedItem<'tcx>, Span, Location),
) {
    MentionedItemsVisitor { tcx, body, mentioned_item }.visit_body(body);
}

impl<'tcx> crate::MirPass<'tcx> for MentionedItems {
    fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
        // If this pass is skipped the collector assume that nothing got mentioned! We could
        // potentially skip it in opt-level 0 if we are sure that opt-level will never *remove* uses
        // of anything, but that still seems fragile. Furthermore, even debug builds use level 1, so
        // special-casing level 0 is just not worth it.
        PassPolicy::Required
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut mir::Body<'tcx>) {
        // Trust: through the shared enumeration (see `for_each_mentioned_item`).
        let mut mentioned_items = Vec::new();
        for_each_mentioned_item(tcx, body, |node, span, _| {
            mentioned_items.push(Spanned { node, span })
        });
        body.set_mentioned_items(mentioned_items);
    }
}

// This visitor is carefully in sync with the one in `rustc_monomorphize::collector`. We are
// visiting the exact same places but then instead of monomorphizing and creating `MonoItems`, we
// have to remain generic and just recording the relevant information in `mentioned_items`, where it
// will then be monomorphized later during "mentioned items" collection.
// Trust: generic over the callback (see `for_each_mentioned_item`).
impl<'tcx, F: FnMut(MentionedItem<'tcx>, Span, Location)> Visitor<'tcx>
    for MentionedItemsVisitor<'_, 'tcx, F>
{
    fn visit_body(&mut self, body: &mir::Body<'tcx>) {
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let mut location = Location { block, statement_index: 0 };
            for statement in &data.statements {
                if let mir::StatementKind::Assign(ref assign) = statement.kind {
                    self.visit_rvalue(&assign.1, location);
                }
                location.statement_index += 1;
            }
            if let Some(ref terminator) = data.terminator {
                self.visit_terminator(terminator, location);
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        let span = terminator.source_info.span;
        match &terminator.kind {
            mir::TerminatorKind::Call { func, .. } | mir::TerminatorKind::TailCall { func, .. } => {
                let callee_ty = func.ty(self.body, self.tcx);
                (self.mentioned_item)(MentionedItem::Fn(callee_ty), span, location);
            }
            mir::TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(self.body, self.tcx).ty;
                (self.mentioned_item)(MentionedItem::Drop(ty), span, location);
            }
            mir::TerminatorKind::InlineAsm { operands, .. } => {
                for op in operands {
                    match *op {
                        mir::InlineAsmOperand::SymFn { ref value } => {
                            (self.mentioned_item)(
                                MentionedItem::Fn(value.const_.ty()),
                                span,
                                location,
                            );
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        match *rvalue {
            // We need to detect unsizing casts that required vtables.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                ref operand,
                target_ty,
            ) => {
                // This isn't monomorphized yet so we can't tell what the actual types are -- just
                // add everything that may involve a vtable.
                let source_ty = operand.ty(self.body, self.tcx);
                let may_involve_vtable = match (
                    source_ty.builtin_deref(true).map(|t| t.kind()),
                    target_ty.builtin_deref(true).map(|t| t.kind()),
                ) {
                    // &str/&[T] unsizing
                    (Some(ty::Array(..)), Some(ty::Str | ty::Slice(..))) => false,

                    _ => true,
                };
                if may_involve_vtable {
                    let span = self.body.source_info(location).span;
                    (self.mentioned_item)(
                        MentionedItem::UnsizeCast { source_ty, target_ty },
                        span,
                        location,
                    );
                }
            }
            // Similarly, record closures that are turned into function pointers.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_), _),
                ref operand,
                _,
            ) => {
                let span = self.body.source_info(location).span;
                let source_ty = operand.ty(self.body, self.tcx);
                (self.mentioned_item)(MentionedItem::Closure(source_ty), span, location);
            }
            // And finally, function pointer reification casts.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_), _),
                ref operand,
                _,
            ) => {
                let span = self.body.source_info(location).span;
                let fn_ty = operand.ty(self.body, self.tcx);
                (self.mentioned_item)(MentionedItem::Fn(fn_ty), span, location);
            }
            _ => {}
        }
    }
}
