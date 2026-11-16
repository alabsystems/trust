//! Scalar foreign-call routing facts. This is no body or contract authority.
use trust_ir::{CallingConv, FuncId, Module, Ty};
use trust_ir::signature_abi::AbiPassMode;

pub(crate) fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Ptr | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::Isize
        | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::Usize | Ty::F32 | Ty::F64)
}

/// Structural route selection only. Admission later re-reads the original
/// source Item/FnAbi; Compiler::compile independently validates physical ABI.
pub(crate) fn recorded(module: &Module, id: FuncId) -> bool {
    let Some(function) = module.function_by_id(id) else { return false; };
    let Some(signature) = module.func_type(function.ty) else { return false; };
    let Ok(Some(view)) = function.fn_abi(module) else { return false; };
    let abi = view.placement();
    function.is_declaration() && function.calling_conv == CallingConv::C
        && abi.convention == "C" && matches!(abi.source_abi.as_str(), "C" | "system" | "cdecl")
        && !abi.can_unwind && abi.fixed_count as usize == signature.params.len()
        && abi.arguments.len() == signature.params.len()
        && signature.returns.len() <= 1
        && signature.params.iter().chain(&signature.returns).all(scalar)
        && abi.arguments.iter().all(|arg| matches!(arg.mode, AbiPassMode::Direct(_)))
        && matches!((&abi.result.mode, signature.returns.len()),
            (AbiPassMode::Direct(_), 1) | (AbiPassMode::Ignore, 0))
        && function.summary.is_none() && function.proofs.is_empty()
        && !module.proof_obligations.iter().any(|o| o.function == Some(id))
}
