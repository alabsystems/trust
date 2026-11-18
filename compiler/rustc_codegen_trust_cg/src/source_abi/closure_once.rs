//! Trust: the exact physical ABI of a retained empty ClosureOnce shim.
//!
//! The owned receiver is omitted from the adapter's physical IR parameters only
//! when rustc actually classifies its precise source type as Ignore, size0,
//! align1 and no fields. All apparent arguments, return, attributes and the full
//! original borrowed FnAbi remain checked/retained. No ordinary source RustCall
//! function or other synthesized instance gains this compiler-owned contract.

use super::*;

pub(super) fn validate<'tcx, 'module>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    module: &'module Module,
    id: FuncId,
) -> Result<SourceAbiAgreement<'tcx, 'module>, String> {
    let symbol = tcx.symbol_name(instance).name;
    let selected =
        crate::trust_ir_frontend::instance_assembly::closure_once_handoff(tcx, instance, symbol)?
            .ok_or("native ClosureOnce ABI has no independently licensed typed adapter")?;
    if !std::ptr::eq(module, selected.module.as_ref()) || selected.func_id != id {
        return Err(
            "native ClosureOnce ABI belongs to a different original image or adapter".into()
        );
    }
    let function = module.function_by_id(id).ok_or("native ClosureOnce adapter is missing")?;
    if function.calling_conv != CallingConv::Rust {
        return Err("native ClosureOnce adapter has a non-Rust convention".into());
    }
    let signature =
        module.func_type(function.ty).ok_or("native ClosureOnce signature is missing")?;
    if let Some(reason) = crate::codegen_attrs_issue(&tcx.codegen_instance_attrs(instance.def)) {
        return Err(reason);
    }
    let source = instance
        .args
        .first()
        .and_then(|arg| arg.as_type())
        .ok_or("native ClosureOnce has no owned receiver type")?;
    let ty::Closure(_, args) = *source.kind() else {
        return Err("native ClosureOnce receiver is not its source closure".into());
    };
    let source_sig = tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
    let [tuple] = source_sig.inputs() else {
        return Err("native ClosureOnce source signature has no exact argument tuple".into());
    };
    let ty::Tuple(fields) = tuple.kind() else {
        return Err("native ClosureOnce source arguments are not a concrete tuple".into());
    };
    let abi = tcx
        .fn_abi_of_instance(
            ty::TypingEnv::fully_monomorphized().as_query_input((instance, ty::List::empty())),
        )
        .map_err(|error| format!("native ClosureOnce FnAbi query failed: {error:?}"))?;
    if source_sig.abi() != rustc_abi::ExternAbi::RustCall
        || source_sig.c_variadic()
        || abi.conv != CanonAbi::Rust
        || abi.c_variadic
        || abi.can_unwind
        || abi.fixed_count != 1
        || abi.args.len() != fields.len() + 1
        || signature.params.len() != fields.len()
    {
        return Err(
            "native ClosureOnce does not have its exact non-unwinding RustCall argument ABI".into(),
        );
    }
    let receiver = abi.args.first().ok_or("native ClosureOnce FnAbi lost its owned receiver")?;
    if tcx.erase_and_anonymize_regions(receiver.layout.ty)
        != tcx.erase_and_anonymize_regions(source)
        || !matches!(&receiver.mode, PassMode::Ignore)
        || receiver.layout.size.bytes() != 0
        || receiver.layout.align.bytes() != 1
        || receiver.layout.fields.count() != 0
    {
        return Err(
            "native ClosureOnce receiver is not the actual ignored empty source environment".into(),
        );
    }
    for (index, ((arg, ir), source)) in
        abi.args[1..].iter().zip(&signature.params).zip(fields.iter()).enumerate()
    {
        if tcx.erase_and_anonymize_regions(arg.layout.ty) != tcx.erase_and_anonymize_regions(source)
        {
            return Err(format!(
                "native ClosureOnce argument {index} changed its source tuple field"
            ));
        }
        scalar_arg(tcx, ir, arg, false)
            .map_err(|error| format!("native ClosureOnce argument {index}: {error}"))?;
    }
    match signature.returns.as_slice() {
        [] if crate::ignored_return_abi_ty_supported(&abi.ret) => {}
        [ir] => {
            scalar_arg(tcx, ir, &abi.ret, false)
                .map_err(|error| format!("native ClosureOnce return: {error}"))?;
        }
        _ => return Err("native ClosureOnce result disagrees with the original FnAbi".into()),
    }
    Ok(SourceAbiAgreement {
        source: module,
        function: id,
        fn_abi: abi,
        placement: aarch64_placement(tcx, abi, 1),
        argument_start: 1,
        adapter_identity: Some(ClosureOnceAdapterIdentity {
            source: selected.module,
            function: id,
        }),
    })
}

// Trust: these pure controls grant no live rustc/native qualification.
#[cfg(test)]
#[path = "closure_once/tests.rs"]
mod tests;
