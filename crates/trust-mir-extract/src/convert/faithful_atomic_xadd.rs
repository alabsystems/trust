// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Faithful diagnostic metadata for ONE compiler intrinsic. This is not an
//! atomic execution model, operation-legality proof, or bridge admission token.

use rustc_abi::Size;
use rustc_middle::ty::{TyCtxt, TypeVisitableExt};
use rustc_middle::{mir, ty};
use rustc_span::sym;
use trust_types::{AtomicOpKind, AtomicOperation, AtomicOrdering, Operand, Place, SourceSpan};

/// `None` leaves every existing parser path unchanged. A recognized intrinsic
/// with malformed/unresolved inputs returns `Some(Err)` and MUST NOT fall back
/// to guessing its ordering from a rendered name or collision suffix.
pub(crate) fn metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &mir::Operand<'tcx>,
    operands: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<Result<AtomicOperation, &'static str>> {
    if !crate::ty_convert::faithful_scalars() {
        return None;
    }
    let (did, args) = func.const_fn_def()?;
    let intrinsic = tcx.intrinsic(did)?;
    if intrinsic.name != sym::atomic_xadd {
        return None;
    }
    Some((|| {
        if !intrinsic.must_be_overridden
            || !super::is_real_sysroot_crate(tcx, did.krate)
            || tcx.lang_items().sized_trait().map(|anchor| anchor.krate) != Some(did.krate)
        {
            return Err("atomic_xadd is not the compiler's authenticated core intrinsic");
        }
        if args.has_non_region_param()
            || args.has_non_region_infer()
            || args.has_non_region_placeholders()
            || args.has_escaping_bound_vars()
        {
            return Err("atomic_xadd generic arguments are not concrete");
        }
        let [memory_ty, operand_ty, ordering] = args.as_slice() else {
            return Err("atomic_xadd requires exactly two type arguments and one ordering");
        };
        let memory_ty = memory_ty.as_type().ok_or("atomic_xadd first argument is not a type")?;
        let operand_ty = operand_ty.as_type().ok_or("atomic_xadd second argument is not a type")?;
        if !((matches!(memory_ty.kind(), ty::Int(_) | ty::Uint(_)) && memory_ty == operand_ty)
            || (memory_ty.is_raw_ptr() && operand_ty == tcx.types.usize))
        {
            return Err("atomic_xadd requires equal integer types or pointer/usize arguments");
        }
        let ordering = ordering.as_const().ok_or("atomic_xadd ordering argument is not a const")?;
        let generics = tcx.generics_of(did);
        let Some(parameter) = generics.own_params.get(2) else {
            return Err("atomic_xadd declaration has no ordering parameter");
        };
        if generics.parent_count != 0
            || generics.own_params.len() != 3
            || parameter.index != 2
            || !matches!(parameter.kind, ty::GenericParamDefKind::Const { .. })
        {
            return Err("atomic_xadd declaration has an unexpected generic signature");
        }
        // The expected type comes from the authenticated declaration itself,
        // never from the string "AtomicOrdering" or an integer surrogate.
        // Do not normalize here: the decoder requires this exact concrete enum
        // type and refuses an alias rather than forcing a new compiler query.
        let expected = tcx.type_of(parameter.def_id).instantiate(tcx, args).skip_normalization();
        let ordering = decode_ordering(tcx, ordering, expected)?;
        let [pointer, _value] = operands else {
            return Err("atomic_xadd requires exactly pointer and value operands");
        };
        let place = match pointer {
            Operand::Copy(place) | Operand::Move(place) => place.clone(),
            _ => return Err("atomic_xadd pointer operand has no representable place"),
        };
        Ok(AtomicOperation {
            place,
            dest: Some(dest.clone()),
            op_kind: AtomicOpKind::FetchAdd,
            ordering,
            failure_ordering: None,
            span: span.clone(),
        })
    })())
}

#[cfg(test)]
pub(crate) fn malformed_cannot_use_legacy_fallback<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &mir::Operand<'tcx>,
    operands: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> bool {
    // Deliberately misleading display text: the real FnDef must win over a
    // name that the legacy parser would otherwise accept as Relaxed.
    matches!(
        super::atomic_metadata_for_call(
            tcx,
            func,
            "core::intrinsics::atomic_xadd_relaxed",
            operands,
            dest,
            span,
        ),
        super::AtomicIntrinsicMetadata::Malformed { .. }
    )
}

fn decode_ordering<'tcx>(
    tcx: TyCtxt<'tcx>,
    ordering: ty::Const<'tcx>,
    expected: ty::Ty<'tcx>,
) -> Result<AtomicOrdering, &'static str> {
    // Read only an already evaluated compiler const. In particular this does
    // not force CTFE from a frozen mir_built provider or normalize a parameter.
    let value = ordering.try_to_value().ok_or("atomic_xadd ordering is not an evaluated value")?;
    if value.ty != expected || !matches!(expected.kind(), ty::Adt(def, _) if def.is_enum()) {
        return Err("atomic_xadd ordering has the wrong compiler enum type");
    }
    let branch = value.try_to_branch().ok_or("atomic_xadd ordering is not an enum branch")?;
    let [discriminant] = branch else {
        return Err("atomic_xadd ordering enum has an unexpected branch shape");
    };
    let discriminant = discriminant
        .try_to_value()
        .ok_or("atomic_xadd ordering discriminator is not an evaluated value")?;
    if discriminant.ty != tcx.types.u32 {
        return Err("atomic_xadd ordering discriminator is not compiler u32");
    }
    let scalar =
        discriminant.try_to_leaf().ok_or("atomic_xadd ordering discriminator is not scalar")?;
    if scalar.size() != Size::from_bytes(4) {
        return Err("atomic_xadd ordering discriminator has the wrong width");
    }
    let bits = scalar.to_bits(Size::from_bytes(4));
    match bits {
        0 => Ok(AtomicOrdering::Relaxed),
        1 => Ok(AtomicOrdering::Release),
        2 => Ok(AtomicOrdering::Acquire),
        3 => Ok(AtomicOrdering::AcqRel),
        4 => Ok(AtomicOrdering::SeqCst),
        _ => Err("atomic_xadd ordering discriminator is unknown"),
    }
}
