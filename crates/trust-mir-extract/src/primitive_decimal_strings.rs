//! The existing ToString totality admission owns this narrower numeric contract.
//! Real compiler facts stay beside the lowered function, never in serialized MIR.

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_types::{BlockId, Ty, VerifiableFunction};
use trust_vcgen::PrimitiveDecimalStringTable;

pub(crate) fn collect<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    lowered: &VerifiableFunction,
) -> PrimitiveDecimalStringTable {
    // Most functions have no admitted call: do not serialize their body for an
    // empty table. Bind lazily only after the real producer admits a primitive.
    let mut table: Option<PrimitiveDecimalStringTable> = None;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Call { func, args, destination, target: Some(_), .. } =
            &data.terminator().kind
        else {
            continue;
        };
        if args.len() != 1 {
            continue;
        }
        let Some((def_id, generic_args)) = func.const_fn_def() else {
            continue;
        };
        let Some(self_ty) =
            crate::convert::authenticated_total_to_string_self_ty(tcx, def_id, generic_args)
        else {
            continue;
        };
        let primitive = match self_ty.kind() {
            ty::Int(kind) => {
                Ty::Int { width: crate::ty_convert::int_width_from_int_ty(kind, tcx), signed: true }
            }
            ty::Uint(kind) => Ty::Int {
                width: crate::ty_convert::uint_width_from_uint_ty(kind, tcx),
                signed: false,
            },
            _ => continue,
        };
        // The instantiated Self and actual call operand must agree exactly. No
        // reference peeling, generic-position guess, float or ADT admission.
        let receiver = args[0].node.ty(&body.local_decls, tcx);
        if !matches!(receiver.kind(), ty::Ref(_, inner, mir::Mutability::Not) if *inner == self_ty)
        {
            continue;
        }
        // The residency-authenticated trait returns std String. Its actual
        // Freeze result licenses ignoring only the lowered opaque/Seq type's
        // conservative shared-cell approximation, never a mutable/raw alias.
        let output = destination.ty(&body.local_decls, tcx).ty;
        if output.has_non_region_param() || !output.is_freeze(tcx, body.typing_env(tcx)) {
            continue;
        }
        let id = BlockId(block.as_usize());
        let Some(lowered_block) = lowered.body.blocks.iter().find(|b| b.id == id) else {
            continue;
        };
        table
            .get_or_insert_with(|| PrimitiveDecimalStringTable::for_function(lowered))
            .record_authenticated_call(id, &lowered_block.terminator, primitive, true);
    }
    table.unwrap_or_default()
}
