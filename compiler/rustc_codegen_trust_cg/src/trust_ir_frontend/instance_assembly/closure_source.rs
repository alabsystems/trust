//! Trust: authenticate a concrete typed Fn/FnOnce body already present in the source handoff.
//!
//! The caller establishes Rust source identity and region-only parent arguments.
//! This check preserves the existing module/table image; it creates no function,
//! adapter, layout or proof authority.

use trust_ir::{BodyGate, CallingConv, FuncId, Module, Producer, Ty};

pub(super) fn validate(
    module: &Module,
    id: FuncId,
    symbol: &str,
    source_capture_count: usize,
    source_authority: &str,
) -> Result<(), String> {
    let function = source_function(module, id, symbol, source_authority)?;
    let body = module.func_type(function.ty).ok_or("source closure signature is missing")?;
    let Some(Ty::Closure(id)) = body.params.first() else {
        return Err("source FnOnce body must receive its typed closure environment by value".into());
    };
    let closure = module.closure_type(*id).ok_or("source closure type is missing")?;
    if closure.captures.len() != source_capture_count {
        return Err("source closure capture count disagrees with rustc's source type".into());
    }
    let apparent =
        module.func_type(closure.func).ok_or("source closure call signature is missing")?;
    if body.is_vararg
        || apparent.is_vararg
        || body.abi.is_some()
        || apparent.abi.is_some()
        || body.params[1..] != apparent.params
        || body.returns != apparent.returns
    {
        return Err(
            "source closure body must have the exact environment-then-arguments signature".into()
        );
    }
    entry_matches(function, body)?;
    module
        .validate_closure_layouts()
        .map_err(|error| format!("source closure layouts are incoherent: {error}"))?;
    let frame = module
        .closure_layout_descriptor(*id)
        .map_err(|error| format!("source closure layout: {error}"))?
        .ok_or("source closure has no observed capture layout")?;
    if source_capture_count == 0
        && (frame.size != 0 || frame.align != 1 || !frame.capture_offsets.is_empty())
    {
        return Err("source empty FnOnce environment is not the exact zero frame".into());
    }
    Ok(())
}

fn source_function<'a>(
    module: &'a Module,
    id: FuncId,
    symbol: &str,
    source_authority: &str,
) -> Result<&'a trust_ir::Function, String> {
    let function = module.function_by_id(id).ok_or("source closure function is missing")?;
    if function.name != symbol {
        return Err("source closure does not carry its exact link-time symbol".into());
    }
    if function.is_declaration() || function.producer != Some(Producer::TRust) {
        return Err("source closure is not a body-bearing Rust source function".into());
    }
    if !matches!(&function.body_gate, Some(BodyGate::Gated { authority, .. }) if authority == source_authority)
    {
        return Err("source closure lacks its direct-source body license".into());
    }
    if function.calling_conv != CallingConv::Rust {
        return Err("source closure does not use the Rust calling convention".into());
    }
    Ok(function)
}

fn entry_matches(function: &trust_ir::Function, body: &trust_ir::FuncTy) -> Result<(), String> {
    let entry = function.block(function.entry).ok_or("source closure entry block is missing")?;
    if entry.params.iter().map(|(_, ty)| ty).ne(body.params.iter()) {
        return Err("source closure entry parameters disagree with its signature".into());
    }
    Ok(())
}

/// A Fn body borrows a source-observed zero environment. The expected nominal
/// identity comes from rustc's actual concrete source type, never from this IR.
pub(super) fn validate_borrowed_zero(
    module: &Module,
    id: FuncId,
    symbol: &str,
    expected_origin: &trust_ir::ty::TypeOrigin,
    source_authority: &str,
) -> Result<(), String> {
    let function = source_function(module, id, symbol, source_authority)?;
    let body = module.func_type(function.ty).ok_or("source closure signature is missing")?;
    module.validate_closure_layouts().map_err(|e| format!("source zero frame: {e}"))?;
    let mut frames = module
        .closure_layouts
        .iter()
        .filter(|frame| frame.origin.as_ref() == Some(expected_origin));
    let frame = frames.next().ok_or("source zero frame identity is missing")?;
    if frames.next().is_some()
        || frame.size != 0
        || frame.align != 1
        || !frame.capture_offsets.is_empty()
    {
        return Err("source zero frame identity is ambiguous or not empty".into());
    }
    let closure = module.closure_type(frame.closure).ok_or("source zero closure is missing")?;
    let apparent = module.func_type(closure.func).ok_or("source zero call signature is missing")?;
    if !closure.captures.is_empty()
        || body.params.first() != Some(&Ty::Ptr)
        || body.params[1..] != apparent.params
        || body.returns != apparent.returns
        || body.is_vararg
        || apparent.is_vararg
        || body.abi.is_some()
        || apparent.abi.is_some()
    {
        return Err("source zero Fn body must borrow its exact environment before arguments".into());
    }
    entry_matches(function, body)?;
    Ok(())
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "closure_source/tests.rs"]
mod tests;
