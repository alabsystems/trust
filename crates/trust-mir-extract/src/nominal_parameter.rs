// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Live Rust signature/declaration custody, not a source/body proof capability.
//!
//! The constructor queries the actual compiler owner. No `VerifiableFunction`,
//! rendered name, TypeOrigin, digest, serialized record or lowered body can
//! construct this observation. The original MIR/capture producer and its
//! semantic correspondence remain separate obligations.

use std::marker::PhantomData;
use std::rc::Rc;

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefPathHash, LocalDefId};

/// Bounded first profile: a direct, nongeneric function parameter whose actual
/// type is a nongeneric fieldless enum. This is not an enum input-domain proof,
/// a discriminant/layout observation, or authentication of external captures.
/// It is affine and confined to the original compiler thread/context.
pub struct NominalParameterObservation<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    argument: usize,
    source_ty: ty::Ty<'tcx>,
    declaration: ty::AdtDef<'tcx>,
    _not_send_sync: PhantomData<Rc<()>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NominalParameterRefusal {
    NotFunction,
    GenericFunction,
    ArgumentBound,
    NotByValueEnum,
    GenericEnum,
    VariantBound,
    PayloadVariant,
}

impl<'tcx> NominalParameterObservation<'tcx> {
    pub(crate) fn context(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    pub fn owner(&self) -> LocalDefId {
        self.owner
    }
    /// Zero-based signature argument, not a MIR local or a diagnostic binder.
    pub fn argument(&self) -> usize {
        self.argument
    }
    pub fn source_ty(&self) -> ty::Ty<'tcx> {
        self.source_ty
    }
    pub fn declaration(&self) -> ty::AdtDef<'tcx> {
        self.declaration
    }
    /// Exported keys are correlation DATA. They cannot recreate this object or
    /// authenticate another context, body, declaration or serialized capture.
    pub fn owner_key(&self) -> DefPathHash {
        self.tcx.def_path_hash(self.owner.to_def_id())
    }
    pub fn nominal_key(&self) -> DefPathHash {
        self.tcx.def_path_hash(self.declaration.did())
    }

    fn same_context(&self, other: &NominalParameterObservation<'_>) -> bool {
        std::ptr::eq(
            std::ptr::from_ref(*self.tcx).cast::<()>(),
            std::ptr::from_ref(*other.tcx).cast::<()>(),
        )
    }
    /// DefId indices alone are not identities across compiler contexts.
    pub fn same_nominal_as(&self, other: &NominalParameterObservation<'_>) -> bool {
        self.same_context(other) && self.declaration.did() == other.declaration.did()
    }
    /// Function owner AND argument ordinal remain part of parameter custody.
    pub fn same_parameter_as(&self, other: &NominalParameterObservation<'_>) -> bool {
        self.same_nominal_as(other) && self.owner == other.owner && self.argument == other.argument
    }
}

/// Observe the original signature via TyCtxt, never from a supplied MIR body.
/// The actual ADT declaration is retained by reference, not reconstructed from
/// a QName or a caller-presented variant/tag list. No discriminant/const-eval,
/// optimized-MIR, layout, trait-normalization or emitter query occurs here.
pub fn observe_nominal_parameter<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    argument: usize,
) -> Result<NominalParameterObservation<'tcx>, NominalParameterRefusal> {
    use NominalParameterRefusal as Refuse;
    if tcx.def_kind(owner) != DefKind::Fn {
        return Err(Refuse::NotFunction);
    }
    if tcx.generics_of(owner).count() != 0 {
        return Err(Refuse::GenericFunction);
    }
    // Only the raw direct ADT signature is observed. A type requiring alias/
    // trait normalization declines below; no normalized semantic fact is used.
    let signature = tcx.fn_sig(owner).instantiate_identity().skip_normalization();
    if !signature.bound_vars().is_empty() {
        return Err(Refuse::GenericFunction);
    }
    let signature = signature.skip_binder();
    if signature.inputs().len() > 128 {
        return Err(Refuse::ArgumentBound);
    }
    let source_ty = *signature.inputs().get(argument).ok_or(Refuse::ArgumentBound)?;
    let ty::Adt(declaration, args) = *source_ty.kind() else {
        return Err(Refuse::NotByValueEnum);
    };
    if !declaration.is_enum() {
        return Err(Refuse::NotByValueEnum);
    }
    if !args.is_empty() || tcx.generics_of(declaration.did()).count() != 0 {
        return Err(Refuse::GenericEnum);
    }
    if declaration.variants().is_empty() || declaration.variants().len() > 256 {
        return Err(Refuse::VariantBound);
    }
    if declaration.variants().iter().any(|variant| !variant.fields.is_empty()) {
        return Err(Refuse::PayloadVariant);
    }
    Ok(NominalParameterObservation {
        tcx,
        owner,
        argument,
        source_ty,
        declaration,
        _not_send_sync: PhantomData,
    })
}
