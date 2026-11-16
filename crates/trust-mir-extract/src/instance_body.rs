// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compiler-owned concrete-instance capture, with no proof or admission claim.
//!
//! A call's syntactic identity and its resolved implementation are deliberately
//! separate. Rendered names cannot establish that association. Likewise an
//! `InstanceKind` (including a closure adapter shim) is part of the identity:
//! extracting a generic definition with a monomorphized label is not enough.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use rustc_hir::def::{CtorKind, DefKind};
use rustc_middle::mir;
use rustc_middle::mir::interpret::GlobalAlloc;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_types::{
    AssertMessage, CalleeIdentity, ConstValue, ConstantImageDefinition, ConstantImageNode, Operand,
    Rvalue, Statement, Terminator, VerifiableFunction,
};

/// An unavailable diagnostic capture is never a successful semantic summary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaithfulInstanceError {
    Frozen,
    Reentrant,
    NotDirectCall,
    NonConcrete,
    ResolutionFailed,
    ResolutionUnavailable,
    Intrinsic,
    Virtual,
    ForeignItem,
    NotCallable,
    MirUnavailable,
    MirSourceMismatch,
    MirInstantiationFailed,
    ResidualParameters,
    AllocationIdentityMismatch,
}

impl fmt::Display for FaithfulInstanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "faithful instance capture unavailable: {self:?}")
    }
}

impl std::error::Error for FaithfulInstanceError {}

/// The compiler's resolution of ONE direct operand in its caller's environment.
/// Trait call-form identities need not equal the resolved impl's identity.
#[derive(Debug)]
pub struct ResolvedFaithfulCall<'tcx> {
    pub syntactic_definition: ConstantImageDefinition,
    pub syntactic_identity: CalleeIdentity,
    pub instance: ty::Instance<'tcx>,
}

/// Actual instantiated MIR and its faithful diagnostic conversion. Unsupported
/// model residue remains present; this record does not certify executability.
#[derive(Debug)]
pub struct FaithfulInstanceBody<'tcx> {
    pub instance: ty::Instance<'tcx>,
    pub mir: mir::Body<'tcx>,
    pub function: VerifiableFunction,
    /// IDs belong only to this extraction's emitted memory images. A function
    /// reference in an initializer does not establish that it executes.
    pub allocation_functions: Vec<(u32, Result<ty::Instance<'tcx>, FaithfulInstanceError>)>,
}

thread_local! {
    static CAPTURING_INSTANCE: Cell<bool> = const { Cell::new(false) };
}

struct CaptureGuard(PhantomData<Rc<()>>);

impl CaptureGuard {
    fn enter() -> Result<Self, FaithfulInstanceError> {
        // This API requests optimized MIR, unlike a bounded foreign-constant
        // evaluation. No instance-MIR query is safe while mir_built owns the
        // producer frame, even if the requested item is not itself on its stack.
        if crate::ctfe_reentrancy::frozen() {
            return Err(FaithfulInstanceError::Frozen);
        }
        if CAPTURING_INSTANCE.with(|active| active.replace(true)) {
            return Err(FaithfulInstanceError::Reentrant);
        }
        Ok(Self(PhantomData))
    }
}

impl Drop for CaptureGuard {
    fn drop(&mut self) {
        CAPTURING_INSTANCE.with(|active| active.set(false));
    }
}

fn concrete_instance(instance: ty::Instance<'_>) -> bool {
    // Inspect the WHOLE instance: some shim kinds embed types outside args.
    !instance.has_non_region_param()
        && !instance.has_non_region_infer()
        && !instance.has_non_region_placeholders()
        && !instance.has_escaping_bound_vars()
}

/// Describe a live compiler instance, including its exact shim kind. This is
/// diagnostic identity data, not an authority-bearing serialized body binding.
pub fn faithful_instance_descriptor<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<ConstantImageNode, FaithfulInstanceError> {
    if !concrete_instance(instance) {
        return Err(FaithfulInstanceError::NonConcrete);
    }
    let callee_identity = crate::instance_identity(tcx, instance.def_id(), instance.args)
        .ok_or(FaithfulInstanceError::NonConcrete)?;
    Ok(ConstantImageNode::Function {
        definition: crate::constant_image::definition(tcx, instance.def_id()),
        instance_fingerprint: crate::constant_image::instance_fingerprint(tcx, instance),
        instance_debug: format!("{instance:?}"),
        callee_identity,
    })
}

/// Resolve an actual direct MIR call operand. This does not resolve indirect
/// function pointers or prove anything about the callee's body or effects.
pub fn resolve_faithful_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    operand: &mir::Operand<'tcx>,
) -> Result<ResolvedFaithfulCall<'tcx>, FaithfulInstanceError> {
    let _guard = CaptureGuard::enter()?;
    let (def_id, args) = operand.const_fn_def().ok_or(FaithfulInstanceError::NotDirectCall)?;
    if args.has_escaping_bound_vars() {
        return Err(FaithfulInstanceError::NonConcrete);
    }
    let syntactic_identity =
        crate::instance_identity(tcx, def_id, args).ok_or(FaithfulInstanceError::NonConcrete)?;
    let instance = ty::Instance::try_resolve(tcx, body.typing_env(tcx), def_id, args)
        .map_err(|_| FaithfulInstanceError::ResolutionFailed)?
        .ok_or(FaithfulInstanceError::ResolutionUnavailable)?;
    if !concrete_instance(instance) {
        return Err(FaithfulInstanceError::NonConcrete);
    }
    Ok(ResolvedFaithfulCall {
        syntactic_definition: crate::constant_image::definition(tcx, def_id),
        syntactic_identity,
        instance,
    })
}

/// Obtain the body for the actual resolved instance and apply its substitutions
/// with rustc's instance-aware helper. In particular already-generated concrete
/// shim MIR must not receive the item's generic substitutions a second time.
///
/// Use after compiler analysis, not from a MIR-building provider. Intrinsics,
/// virtual dispatch and missing external MIR are explicit unavailable cases.
/// Unreachable or unsupported bodies are retained as diagnostic data, not
/// admitted as verified implementations.
pub fn extract_instance_faithful<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<FaithfulInstanceBody<'tcx>, FaithfulInstanceError> {
    let _guard = CaptureGuard::enter()?;
    if !concrete_instance(instance) {
        return Err(FaithfulInstanceError::NonConcrete);
    }
    match instance.def {
        ty::InstanceKind::Intrinsic(_) | ty::InstanceKind::LlvmIntrinsic(_) => {
            return Err(FaithfulInstanceError::Intrinsic);
        }
        ty::InstanceKind::Virtual(..) => return Err(FaithfulInstanceError::Virtual),
        ty::InstanceKind::Item(def_id) => {
            if tcx.is_foreign_item(def_id) {
                return Err(FaithfulInstanceError::ForeignItem);
            }
            if !matches!(
                tcx.def_kind(def_id),
                DefKind::Fn
                    | DefKind::AssocFn
                    | DefKind::Ctor(_, CtorKind::Fn)
                    | DefKind::Closure
                    | DefKind::SyntheticCoroutineBody
            ) {
                return Err(FaithfulInstanceError::NotCallable);
            }
            if !tcx.is_mir_available(def_id) {
                return Err(FaithfulInstanceError::MirUnavailable);
            }
        }
        ty::InstanceKind::Shim(_) => {}
    }
    let body = tcx.instance_mir(instance.def);
    if body.source.promoted.is_some()
        || tcx.erase_and_anonymize_regions(body.source.instance)
            != tcx.erase_and_anonymize_regions(instance.def)
    {
        return Err(FaithfulInstanceError::MirSourceMismatch);
    }
    let mir = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, body.clone()),
        )
        .map_err(|_| FaithfulInstanceError::MirInstantiationFailed)?;
    if mir.has_non_region_param()
        || mir.has_non_region_infer()
        || mir.has_non_region_placeholders()
        || mir.has_escaping_bound_vars()
    {
        return Err(FaithfulInstanceError::ResidualParameters);
    }
    if tcx.erase_and_anonymize_regions(mir.source.instance)
        != tcx.erase_and_anonymize_regions(instance.def)
    {
        return Err(FaithfulInstanceError::MirSourceMismatch);
    }
    let (function, allocation_functions) =
        extract_faithful_body_with_function_allocations(tcx, &mir);
    Ok(FaithfulInstanceBody { instance, mir, function, allocation_functions })
}

/// Extract exactly the supplied body, without normalizing or replacing it.
/// Retain live compiler function instances only for matching Function nodes in
/// successfully emitted memory images. Allocations reserved by a failed image
/// are not call-graph edges. This is not a complete executable call graph.
pub fn extract_faithful_body_with_function_allocations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> (VerifiableFunction, Vec<(u32, Result<ty::Instance<'tcx>, FaithfulInstanceError>)>) {
    let (function, allocations) = crate::extract_function_faithful_with_allocations(tcx, body);
    let nodes = emitted_function_nodes(&function);
    let functions = nodes
        .into_iter()
        .map(|(id, node)| {
            let resolved = (|| {
                let mismatch = FaithfulInstanceError::AllocationIdentityMismatch;
                let node = node.ok_or(mismatch)?;
                let index = usize::try_from(id).map_err(|_| mismatch)?;
                let allocation = *allocations.get(index).ok_or(mismatch)?;
                let GlobalAlloc::Function { instance } =
                    tcx.try_get_global_alloc(allocation).ok_or(mismatch)?
                else {
                    return Err(mismatch);
                };
                // Includes the definition hash, full instance-kind fingerprint
                // and callee identity; no rendered-name fallback. Disagreement
                // remains an explicit unavailable edge, never a silent omission.
                let actual = faithful_instance_descriptor(tcx, instance)?;
                if node != actual {
                    return Err(mismatch);
                }
                Ok(instance)
            })();
            (id, resolved)
        })
        .collect();
    (function, functions)
}

fn operand_constants<'a>(operand: &'a Operand, values: &mut Vec<&'a ConstValue>) {
    if let Operand::Constant(value) = operand {
        values.push(value);
    }
}

fn rvalue_constants<'a>(rvalue: &'a Rvalue, values: &mut Vec<&'a ConstValue>) {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            operand_constants(op, values);
        }
        Rvalue::BinaryOp(_, left, right)
        | Rvalue::CheckedBinaryOp(_, left, right)
        | Rvalue::UncheckedBinaryOp(_, left, right)
        | Rvalue::PtrOffset { ptr: left, count: right } => {
            operand_constants(left, values);
            operand_constants(right, values);
        }
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            for operand in operands {
                operand_constants(operand, values);
            }
        }
        Rvalue::Ref { .. }
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::AddressOf(..)
        | Rvalue::CopyForDeref(_) => {}
        // The model is non_exhaustive outside trust-types. Unknown future
        // variants do not acquire invented edges or a completeness claim.
        _ => {}
    }
}

fn assert_message_constants<'a>(message: &'a AssertMessage, _values: &mut Vec<&'a ConstValue>) {
    // The owning crate's constant_image.rs census has no operand-valued
    // AssertMessage fields today. Keep the known variants visible here too.
    match message {
        AssertMessage::BoundsCheck
        | AssertMessage::Overflow(_)
        | AssertMessage::OverflowNeg
        | AssertMessage::DivisionByZero
        | AssertMessage::RemainderByZero
        | AssertMessage::ResumedAfterReturn
        | AssertMessage::ResumedAfterPanic
        | AssertMessage::ResumedAfterDrop
        | AssertMessage::MisalignedPointerDereference
        | AssertMessage::NullPointerDereference
        | AssertMessage::InvalidEnumConstruction
        | AssertMessage::Custom(_) => {}
        _ => {}
    }
}

fn emitted_function_nodes(
    function: &VerifiableFunction,
) -> BTreeMap<u32, Option<ConstantImageNode>> {
    let mut values = Vec::new();
    for block in &function.body.blocks {
        for statement in &block.stmts {
            match statement {
                Statement::Assign { rvalue, .. } => rvalue_constants(rvalue, &mut values),
                Statement::Intrinsic { args: operands, .. }
                | Statement::Unsupported { operands, .. } => {
                    for operand in operands {
                        operand_constants(operand, &mut values);
                    }
                }
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    for operand in [src, dst, count] {
                        operand_constants(operand, &mut values);
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::SwitchInt { discr, .. } => {
                operand_constants(discr, &mut values);
            }
            Terminator::Assert { cond, msg, .. } => {
                operand_constants(cond, &mut values);
                assert_message_constants(msg, &mut values);
            }
            Terminator::Call { args, .. } | Terminator::TailCall { args, .. } => {
                for operand in args {
                    operand_constants(operand, &mut values);
                }
            }
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Drop { .. }
            | Terminator::Opaque { .. }
            | Terminator::Unreachable
            | Terminator::Resume => {}
            _ => {}
        }
    }
    let mut nodes: BTreeMap<u32, Option<ConstantImageNode>> = BTreeMap::new();
    while let Some(value) = values.pop() {
        match value {
            ConstValue::StructScalarFieldsRef { fields, .. } => values.extend(fields),
            ConstValue::MemoryImage(image) => {
                for (&id, node) in &image.nodes {
                    if matches!(node, ConstantImageNode::Function { .. }) {
                        nodes
                            .entry(id)
                            .and_modify(|prior| {
                                if prior.as_ref() != Some(node) {
                                    *prior = None;
                                }
                            })
                            .or_insert_with(|| Some(node.clone()));
                    }
                }
            }
            _ => {}
        }
    }
    nodes
}
