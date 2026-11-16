//! Compiler-owned relaxed fetch-add lowering. The public data-only bridge
//! remains closed to every atomic metadata claim. The compiler capability
//! chooses the actual operation; it does not discharge its safety conditions.

use trust_ir::inst::{AtomicRMWOp, Ordering};
use trust_types::{AtomicOpKind, AtomicOrdering, UnwindEdge};

use super::*;

/// Lower the exact, immutable body freshly captured by the compiler extractor.
///
/// No caller-supplied `VerifiableFunction`, serialized metadata, or transferable
/// callsite token is accepted. Unauthenticated atomic sites still refuse the
/// whole lowering. Each emitted RMW retains separate pending memory-safety and
/// ownership obligations. This is not a source-refinement certificate, a
/// concurrency theorem, or permission to enter a certified execution lane.
#[cfg(feature = "compiler-context")]
pub fn lower_compiler_relaxed_xadd_u64_body(
    captured: &trust_mir_extract::atomic_callsite::CompilerRelaxedXaddBody<'_>,
) -> Result<Module, BridgeError> {
    let function = captured.function();
    let blocks = captured.sites().iter().map(|site| site.block()).collect();
    lower_owned_function(function, &blocks, captured.target_llvm_triple())
}

// This seam is deliberately private. Its only production caller obtains ALL
// arguments from the same opaque compiler owner above. Unit tests can exercise
// lowering mechanics here, but cannot grant authority through any public API.
#[cfg(any(feature = "compiler-context", test))]
fn lower_owned_function(
    function: &VerifiableFunction,
    blocks: &FxHashSet<BlockId>,
    target_llvm_triple: &str,
) -> Result<Module, BridgeError> {
    reject_memory_image_body(function)?;
    let mut module = Module::new(&function.name);
    // The owner minted these facts only after checking the compiler's target
    // and u64/usize layouts. Preserve them even when the function uses usize;
    // no aggregate calling-convention classification is implied.
    module.target_info = Some(trust_ir::TargetInfo {
        triple: target_llvm_triple.to_owned(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let closure_env_types = collect_closure_env_types(&[function])?;
    let mut known_functions = FxHashMap::default();
    register_function_name(&mut known_functions, function, FuncId::new(0));
    let mut known_signatures = FxHashMap::default();
    register_function_signature(
        &mut known_signatures,
        function,
        FuncId::new(0),
        &closure_env_types,
    )?;
    let empty = FxHashSet::default();
    let mut type_cache = FxHashMap::default();
    let mut tuple_ledger = TupleLayoutLedger::default();
    let lowered = lower_function_into(
        function,
        &mut module,
        &known_functions,
        &known_signatures,
        &closure_env_types,
        &mut type_cache,
        &mut tuple_ledger,
        &empty,
        &empty,
        &empty,
        &empty,
        &empty,
        &empty,
        &FxHashSet::default(),
        &empty,
        &FxHashSet::default(), // no drop-reach withdrawals
        &crate::lower::CallReachWithdrawals::default(), // no call-reach withdrawals
        // No borrow-validity authority is implied by operation recognition.
        Some(&empty),
        blocks,
        &super::InstanceHypothesisSites::default(),
        &super::CompilerAllocGrowPins::default(),
    )?;
    module.try_add_function(lowered)?;
    Ok(module)
}

pub(super) fn lower_relaxed_xadd(
    block: BlockId,
    term: &Terminator,
    ctx: &mut LoweringCtx<'_>,
    body: &mut Vec<InstrNode>,
) -> Result<(), BridgeError> {
    let Terminator::Call {
        func,
        args,
        dest,
        target: Some(_),
        atomic: Some(atomic),
        unwind: UnwindEdge::Unreachable,
        span,
        ..
    } = term
    else {
        return Err(BridgeError::UnsupportedOp(
            "atomic call lacks compiler-authenticated operation and ordering evidence".into(),
        ));
    };
    if !ctx.compiler_relaxed_xadd_blocks.contains(&block) {
        return Err(BridgeError::UnsupportedOp(format!(
            "atomic call `{func}` lacks compiler-authenticated operation and ordering evidence"
        )));
    }
    // Recheck the lowering envelope after the bridge's physical-type view.
    // These checks alone confer no authority: the private block set above is
    // required even if a public model forges every field below perfectly.
    let [pointer, increment] = args.as_slice() else {
        return Err(BridgeError::UnsupportedOp("authenticated xadd operand drift".into()));
    };
    let pointer_place = match pointer {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place,
        _ => return Err(BridgeError::UnsupportedOp("authenticated xadd pointer drift".into())),
    };
    let value_ty = place_type(dest, ctx)?;
    if !dest.projections.is_empty()
        || !matches!(
            value_ty,
            Ty::Int { width: 64, signed: false } | Ty::PtrSizedInt { signed: false }
        )
        || operand_trust_type(pointer, ctx)?
            != (Ty::RawPtr { mutable: true, pointee: Box::new(value_ty.clone()) })
        || atomic.op_kind != AtomicOpKind::FetchAdd
        || atomic.ordering != AtomicOrdering::Relaxed
        || atomic.failure_ordering.is_some()
        || atomic.place != *pointer_place
        || atomic.dest.as_ref() != Some(dest)
    {
        return Err(BridgeError::UnsupportedOp("authenticated xadd type/metadata drift".into()));
    }
    let pointer = ctx.resolve_operand(pointer, body)?;
    let increment = ctx.resolve_operand_as_trust_type(increment, &value_ty, body)?;
    let result = ctx.fresh_value();
    let ty = ctx.map_type_ctx(&value_ty)?;
    body.push(
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty,
            ptr: pointer,
            value: increment,
            ordering: Ordering::Relaxed,
        })
        .with_result(result),
    );
    // Mint before assign_value_to_place can append a store: both obligations
    // concern this very RMW, not its continuation or the destination assignment.
    for (kind, class, requirement) in [
        (
            ObligationKind::MemorySafety,
            "memory",
            "a live, initialized, writable, 8-byte-aligned u64 allocation",
        ),
        (
            ObligationKind::Ownership,
            "ownership",
            "compatible atomic accesses and an explicit concurrent or exclusive sequential memory invariant",
        ),
    ] {
        let description =
            format!("compiler-authenticated relaxed xadd `{func}` still requires {requirement}");
        let source_id =
            format!("mir-atomic:{class}:{}:bb{}:terminator", ctx.function_def_path, block.0);
        let assertion_id = format!("trust-assertion:{source_id}");
        let source = ObligationSourceMetadata {
            native_assertion_id: trust_types::stable_u32_id(assertion_id.as_bytes()),
            source_id,
            assertion_id,
            span: span.clone(),
            predicate: None,
            safety_predicate: None,
        };
        ctx.add_obligation_for_last_inst(kind, description, source, body)?;
    }
    ctx.mark_result_symbolic_from(result, &[pointer, increment]);
    assign_value_to_place(dest, result, ctx, body)
}

#[cfg(test)]
#[path = "atomic_bridge_tests.rs"]
mod tests;
