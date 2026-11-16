// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! In-process compiler facts for the narrow unsigned-64 relaxed fetch-add lane.
//!
//! This owner binds actual compiler MIR to its fresh faithful model. It is NOT
//! a pointer-validity, race-freedom, execution-refinement or kernel certificate.
//! Consumers must lower this owner's immutable function, never combine a site
//! with a caller-supplied/serialized model or treat `Call.atomic` as authority.

use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;

use rustc_abi::{Endian, Size};
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::sym;
use trust_types::{
    AtomicOrdering, BlockId, CalleeIdentity, ConstValue, Operand, Place, SourceSpan, Terminator,
    Ty, UnwindEdge, VerifiableFunction,
};

use crate::instance_body::{FaithfulInstanceError, extract_instance_faithful};

/// Rust's two distinct unsigned scalar types admitted on the pinned LE64 lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicXaddIntegerType {
    U64,
    Usize,
}

impl AtomicXaddIntegerType {
    fn model(self) -> Ty {
        match self {
            Self::U64 => Ty::Int { width: 64, signed: false },
            Self::Usize => Ty::PtrSizedInt { signed: false },
        }
    }
}

/// A refusal is diagnostic data, never a partially admitted operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicCallsiteError {
    Instance(FaithfulInstanceError),
    Target,
    Layout,
    CallShape,
    OperandArity,
    IntegerType,
    PointerType,
    OperandShape,
    ConstantValue,
    Destination,
    ControlFlow,
    Intrinsic(&'static str),
    Ordering,
    ModelMismatch(&'static str),
}

impl fmt::Display for AtomicCallsiteError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "compiler relaxed-u64 fetch-add unavailable: {self:?}; retain the ordinary refusal or extend the compiler-held exact-site checks"
        )
    }
}

impl std::error::Error for AtomicCallsiteError {}

#[derive(Default)]
struct AtomicSessionSeal(Option<Arc<()>>);

fn session_seal(tcx: TyCtxt<'_>) -> Arc<()> {
    tcx.sess.with_trust_compiler_state::<AtomicSessionSeal, _>(|state| {
        Arc::clone(state.0.get_or_insert_with(|| Arc::new(())))
    })
}

/// Constructor-free, non-Clone and non-serializable owner of ONE actual body.
/// No API accepts a public `FaithfulInstanceBody`, takes a model as input, or
/// exposes mutable access/`into_parts`. A cloned model carries no site rights.
#[derive(Debug)]
pub struct CompilerRelaxedXaddBody<'tcx> {
    session_seal: Arc<()>,
    owner_seal: Arc<()>,
    instance: ty::Instance<'tcx>,
    mir: mir::Body<'tcx>,
    function: VerifiableFunction,
    target_triple: String,
    target_llvm_triple: String,
    target_data_layout: String,
    sites: Vec<CompilerRelaxedXaddSite>,
    refusals: Vec<(BlockId, AtomicCallsiteError)>,
    _thread: PhantomData<Rc<()>>,
}

impl<'tcx> CompilerRelaxedXaddBody<'tcx> {
    pub fn function(&self) -> &VerifiableFunction {
        &self.function
    }
    pub fn instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }
    pub fn mir(&self) -> &mir::Body<'tcx> {
        &self.mir
    }
    pub fn target_triple(&self) -> &str {
        &self.target_triple
    }
    pub fn target_llvm_triple(&self) -> &str {
        &self.target_llvm_triple
    }
    pub fn target_data_layout(&self) -> &str {
        &self.target_data_layout
    }
    pub fn sites(&self) -> &[CompilerRelaxedXaddSite] {
        &self.sites
    }
    pub fn refusals(&self) -> &[(BlockId, AtomicCallsiteError)] {
        &self.refusals
    }
    pub fn site(&self, block: BlockId) -> Option<&CompilerRelaxedXaddSite> {
        self.sites.iter().find(|site| site.block == block)
    }

    /// A borrowed site from a different extraction/session cannot be reused.
    /// This authenticates only association with THIS owner, not another model.
    pub fn owns_site(&self, site: &CompilerRelaxedXaddSite) -> bool {
        Arc::ptr_eq(&self.session_seal, &site.session_seal)
            && Arc::ptr_eq(&self.owner_seal, &site.owner_seal)
            && self.sites.iter().any(|candidate| std::ptr::eq(candidate, site))
    }

    /// Test-only differential of the exact-site checks. It returns no owner or
    /// capability and cannot change this owner or exist in production builds.
    #[cfg(test)]
    pub(crate) fn rejects_model_mutation(
        &self,
        tcx: TyCtxt<'tcx>,
        change: impl FnOnce(&mut VerifiableFunction),
    ) -> bool {
        let mut changed = Self {
            session_seal: Arc::clone(&self.session_seal),
            owner_seal: Arc::new(()),
            instance: self.instance,
            mir: self.mir.clone(),
            function: self.function.clone(),
            target_triple: self.target_triple.clone(),
            target_llvm_triple: self.target_llvm_triple.clone(),
            target_data_layout: self.target_data_layout.clone(),
            sites: Vec::new(),
            refusals: Vec::new(),
            _thread: PhantomData,
        };
        change(&mut changed.function);
        let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
        !self.sites.is_empty()
            && self.sites.iter().all(|site| {
                changed
                    .mir
                    .basic_blocks
                    .iter_enumerated()
                    .find(|(bb, _)| bb.as_usize() == site.block.0)
                    .is_some_and(|(bb, data)| check_site(tcx, &changed, bb, data).is_err())
            })
    }
}

/// Compiler-established facts about one Call in its immutable body owner.
/// There is deliberately no standalone constructor, Clone or serde transport.
#[derive(Debug)]
pub struct CompilerRelaxedXaddSite {
    session_seal: Arc<()>,
    owner_seal: Arc<()>,
    block: BlockId,
    integer_type: AtomicXaddIntegerType,
    callee_identity: CalleeIdentity,
    pointer: Operand,
    value: Operand,
    destination: Place,
    target: BlockId,
    span: SourceSpan,
}

impl CompilerRelaxedXaddSite {
    pub fn block(&self) -> BlockId {
        self.block
    }
    pub fn integer_type(&self) -> AtomicXaddIntegerType {
        self.integer_type
    }
    pub fn callee_identity(&self) -> CalleeIdentity {
        self.callee_identity
    }
    pub fn pointer(&self) -> &Operand {
        &self.pointer
    }
    pub fn value(&self) -> &Operand {
        &self.value
    }
    pub fn destination(&self) -> &Place {
        &self.destination
    }
    pub fn target(&self) -> BlockId {
        self.target
    }
    pub fn span(&self) -> &SourceSpan {
        &self.span
    }
}

fn target_supported(tcx: TyCtxt<'_>) -> bool {
    tcx.data_layout.endian == Endian::Little
        && tcx.data_layout.pointer_size().bits() == 64
        && tcx.sess.target.pointer_width == 64
        && tcx.sess.target.min_atomic_width() <= 64
        && tcx.sess.target.max_atomic_width() >= 64
        && tcx.sess.target.atomic_cas
}

/// Query the compiler's actual concrete body and privately retain its exact
/// instance, MIR, fresh model, target and call-site association. Missing bodies
/// and unsupported targets fail; unsupported xadd sites are explicit refusals.
/// Other operations remain in the body, with no new admission attached.
pub fn capture_relaxed_xadd_u64_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<CompilerRelaxedXaddBody<'tcx>, AtomicCallsiteError> {
    if !target_supported(tcx) {
        return Err(AtomicCallsiteError::Target);
    }
    let captured =
        extract_instance_faithful(tcx, instance).map_err(AtomicCallsiteError::Instance)?;
    let mut owner = CompilerRelaxedXaddBody {
        session_seal: session_seal(tcx),
        owner_seal: Arc::new(()),
        instance: captured.instance,
        mir: captured.mir,
        function: captured.function,
        target_triple: tcx.sess.opts.target_triple.to_string(),
        target_llvm_triple: tcx.sess.target.llvm_target.to_string(),
        target_data_layout: tcx.sess.target.data_layout.to_string(),
        sites: Vec::new(),
        refusals: Vec::new(),
        _thread: PhantomData,
    };
    let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
    for (bb, data) in owner.mir.basic_blocks.iter_enumerated() {
        let func = match &data.terminator().kind {
            mir::TerminatorKind::Call { func, .. } | mir::TerminatorKind::TailCall { func, .. } => {
                func
            }
            _ => continue,
        };
        let Some((did, _)) = func.const_fn_def() else { continue };
        if tcx.intrinsic(did).is_none_or(|intrinsic| intrinsic.name != sym::atomic_xadd) {
            continue;
        }
        match check_site(tcx, &owner, bb, data) {
            Ok(site) => owner.sites.push(site),
            Err(error) => owner.refusals.push((BlockId(bb.as_usize()), error)),
        }
    }
    Ok(owner)
}

fn plain_place(place: &mir::Place<'_>) -> Result<Place, AtomicCallsiteError> {
    if !place.projection.is_empty() {
        return Err(AtomicCallsiteError::OperandShape);
    }
    Ok(Place::local(place.local.as_usize()))
}

fn plain_operand(operand: &mir::Operand<'_>) -> Result<Operand, AtomicCallsiteError> {
    match operand {
        mir::Operand::Copy(place) => Ok(Operand::Copy(plain_place(place)?)),
        mir::Operand::Move(place) => Ok(Operand::Move(plain_place(place)?)),
        mir::Operand::Constant(constant) => {
            let scalar = match constant.const_ {
                mir::Const::Val(mir::ConstValue::Scalar(scalar), _) => {
                    scalar.try_to_scalar_int().ok()
                }
                mir::Const::Ty(_, value) => {
                    value.try_to_value().and_then(|value| value.try_to_leaf())
                }
                _ => None,
            }
            .ok_or(AtomicCallsiteError::ConstantValue)?;
            if scalar.size() != Size::from_bytes(8) {
                return Err(AtomicCallsiteError::ConstantValue);
            }
            let bits = scalar.to_bits(Size::from_bytes(8));
            Ok(Operand::Constant(ConstValue::Uint(bits, 64)))
        }
        _ => Err(AtomicCallsiteError::OperandShape),
    }
}

fn same_operand(expected: &Operand, actual: &Operand) -> bool {
    match (expected, actual) {
        (Operand::Copy(left), Operand::Copy(right))
        | (Operand::Move(left), Operand::Move(right)) => left == right,
        (
            Operand::Constant(ConstValue::Uint(left, lw)),
            Operand::Constant(ConstValue::Uint(right, rw)),
        ) => left == right && lw == rw,
        _ => false,
    }
}

fn check_site<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: &CompilerRelaxedXaddBody<'tcx>,
    bb: mir::BasicBlock,
    data: &mir::BasicBlockData<'tcx>,
) -> Result<CompilerRelaxedXaddSite, AtomicCallsiteError> {
    let mir::TerminatorKind::Call { func, args, destination, target, unwind, .. } =
        &data.terminator().kind
    else {
        return Err(AtomicCallsiteError::CallShape);
    };
    let [pointer, value] = args.as_ref() else { return Err(AtomicCallsiteError::OperandArity) };
    let (did, generic_args) = func.const_fn_def().ok_or(AtomicCallsiteError::CallShape)?;
    let [memory_ty, value_ty, _] = generic_args.as_slice() else {
        return Err(AtomicCallsiteError::IntegerType);
    };
    let memory_ty = memory_ty.as_type().ok_or(AtomicCallsiteError::IntegerType)?;
    if value_ty.as_type() != Some(memory_ty) {
        return Err(AtomicCallsiteError::IntegerType);
    }
    let integer_type = if memory_ty == tcx.types.u64 {
        AtomicXaddIntegerType::U64
    } else if memory_ty == tcx.types.usize {
        AtomicXaddIntegerType::Usize
    } else {
        return Err(AtomicCallsiteError::IntegerType);
    };
    let layout =
        crate::tuple_layouts::extractor_layout_of(tcx, owner.mir.typing_env(tcx), memory_ty)
            .ok_or(AtomicCallsiteError::Layout)?;
    if layout.size.bytes() != 8 || layout.align.bytes() != 8 {
        return Err(AtomicCallsiteError::Layout);
    }
    if pointer.node.ty(&owner.mir.local_decls, tcx) != ty::Ty::new_mut_ptr(tcx, memory_ty) {
        return Err(AtomicCallsiteError::PointerType);
    }
    if value.node.ty(&owner.mir.local_decls, tcx) != memory_ty {
        return Err(AtomicCallsiteError::IntegerType);
    }
    if destination.ty(&owner.mir.local_decls, tcx).ty != memory_ty
        || !destination.projection.is_empty()
    {
        return Err(AtomicCallsiteError::Destination);
    }
    let pointer = plain_operand(&pointer.node)?;
    if !matches!(pointer, Operand::Copy(_) | Operand::Move(_)) {
        return Err(AtomicCallsiteError::OperandShape);
    }
    let value = plain_operand(&value.node)?;
    let destination = plain_place(destination)?;
    let span = crate::convert::convert_span(tcx, data.terminator().source_info.span);
    let operands = [pointer.clone(), value.clone()];
    let metadata =
        crate::convert::faithful_atomic_xadd::metadata(tcx, func, &operands, &destination, &span)
            .ok_or(AtomicCallsiteError::Intrinsic("not the recognized compiler intrinsic"))?
            .map_err(AtomicCallsiteError::Intrinsic)?;
    if metadata.ordering != AtomicOrdering::Relaxed {
        return Err(AtomicCallsiteError::Ordering);
    }
    // Authenticate the intrinsic before checking its eligible continuation:
    // an unauthorized declaration must not hide behind its different unwind
    // behavior. Both checks remain mandatory before any site is admitted.
    let Some(target) = *target else { return Err(AtomicCallsiteError::ControlFlow) };
    if owner.mir.basic_blocks.get(target).is_none() || *unwind != mir::UnwindAction::Unreachable {
        return Err(AtomicCallsiteError::ControlFlow);
    }
    let identity = crate::convert::callee_identity_for(tcx, did, generic_args)
        .ok_or(AtomicCallsiteError::Intrinsic("non-concrete compiler call identity"))?;
    let model_block = owner
        .function
        .body
        .blocks
        .get(bb.as_usize())
        .filter(|block| block.id.0 == bb.as_usize())
        .ok_or(AtomicCallsiteError::ModelMismatch("block identity"))?;
    let Terminator::Call {
        func: model_name,
        args: model_args,
        dest: model_dest,
        target: model_target,
        span: model_span,
        atomic,
        is_foreign,
        is_unsafe_sig,
        callee_identity,
        callee_key,
        unwind: model_unwind,
    } = &model_block.terminator
    else {
        return Err(AtomicCallsiteError::ModelMismatch("not a faithful Call"));
    };
    if *model_name != crate::convert::func_operand_name_in_body(tcx, &owner.mir, func)
        || *callee_identity != Some(identity)
        || *callee_key != Some(crate::convert::callee_key_for(tcx, did))
        || *is_foreign
        || !*is_unsafe_sig
        || model_args.len() != 2
        || !same_operand(&pointer, &model_args[0])
        || !same_operand(&value, &model_args[1])
        || model_dest != &destination
        || *model_target != Some(BlockId(target.as_usize()))
        || model_span != &span
        || *model_unwind != UnwindEdge::Unreachable
        || atomic.as_ref() != Some(&metadata)
    {
        return Err(AtomicCallsiteError::ModelMismatch(
            "callee, operands, destination, control flow or metadata",
        ));
    }
    let scalar_ty = integer_type.model();
    let pointer_ty = Ty::RawPtr { mutable: true, pointee: Box::new(scalar_ty.clone()) };
    for (operand, expected_ty) in [(&pointer, &pointer_ty), (&value, &scalar_ty)] {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if owner
                .function
                .body
                .locals
                .get(place.local)
                .is_none_or(|decl| decl.ty != *expected_ty)
            {
                return Err(AtomicCallsiteError::ModelMismatch("operand local type"));
            }
        }
    }
    if owner.function.body.locals.get(destination.local).is_none_or(|decl| decl.ty != scalar_ty) {
        return Err(AtomicCallsiteError::ModelMismatch("destination local type"));
    }
    Ok(CompilerRelaxedXaddSite {
        session_seal: Arc::clone(&owner.session_seal),
        owner_seal: Arc::clone(&owner.owner_seal),
        block: BlockId(bb.as_usize()),
        integer_type,
        callee_identity: identity,
        pointer,
        value,
        destination,
        target: BlockId(target.as_usize()),
        span,
    })
}
