//! Placement of compiler-defined typed closure adapters, never rustc instances.
//!
//! A conserved non-source ID is licensed only under the exact handoff binding.
//! Recheck its complete constructor protocol and admitted source endpoints
//! before interpreting its flat internal signature. No display-name heuristic,
//! synthetic DefIndex, source coverage row or rustc FnAbi is manufactured.

use trust_cg_bridge::call_event::{AbiExt, ParamPlace, ReturnPlace, ScalarPlace, Slot};
use trust_ir::{CallingConv, ClosureTyId, FuncTy, Ty};

use super::*;

fn width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 => Some(16),
        Ty::I32 | Ty::U32 | Ty::Char => Some(32),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize | Ty::Ptr => Some(64),
        _ => None,
    }
}

fn flat_placement(signature: &FuncTy) -> Option<FnPlacement> {
    if signature.is_vararg || signature.abi.is_some() || signature.params.len() > 8 {
        return None;
    }
    let params = signature
        .params
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            Some(ParamPlace::Scalar(ScalarPlace::gpr(u8::try_from(i).ok()?, width(ty)?)))
        })
        .collect::<Option<Vec<_>>>()?;
    let ret = match signature.returns.as_slice() {
        [] => ReturnPlace::Void,
        [ty] => ReturnPlace::Scalar(ScalarPlace::gpr(0, width(ty)?)),
        _ => return None,
    };
    Some(FnPlacement { params, ret })
}

fn source_item<'a>(
    input: &'a NativeModuleInput<'_>,
    id: FuncId,
) -> Result<&'a NativeWorkItem, String> {
    let body = input.producer.function_by_id(id).ok_or("adapter source endpoint is missing")?;
    if !input.source_ids.contains(&id)
        || !input.conserved.contains(&id)
        || body.is_declaration()
        || body.producer != Some(Producer::TRust)
    {
        return Err("adapter endpoint is not an independently conserved source body".into());
    }
    let item = input
        .items
        .iter()
        .find(|item| item.func == id)
        .ok_or("adapter source endpoint has no selected actual source ABI")?;
    if item.symbol != body.name {
        return Err("adapter source endpoint symbol differs from its selected source ABI".into());
    }
    Ok(item)
}

/// The exact canonical function emitted by closure_adapter::build. Equality
/// includes instructions, types, SSA IDs, producer, linkage, attrs and metadata;
/// only the later publication gate is removed for this structural comparison.
fn protocol(
    input: &NativeModuleInput<'_>,
    id: FuncId,
) -> Result<(ClosureTyId, FuncId, bool), String> {
    let module = input.producer;
    if !matches!(input.base, Some(base) if base == module)
        || input.source_ids.contains(&id)
        || !input.conserved.contains(&id)
    {
        return Err("adapter placement has no exact conserved non-source handoff identity".into());
    }
    let adapter = module.function_by_id(id).ok_or("adapter function is missing")?;
    if module.functions.iter().filter(|f| f.name == adapter.name).count() != 1 {
        return Err("adapter link symbol is ambiguous".into());
    }
    // One owner defines the full typed protocol. Native placement must not
    // maintain a second constructor that drifts from source assembly.
    let shape = trust_thir_lower::closure_adapter::inspect(
        adapter,
        &module.closure_types,
        &module.func_types,
    )
    .ok_or("adapter differs from the canonical typed construction protocol")?;
    let closure = shape.closure;
    let target = shape.body;
    let declaration = module.closure_type(closure).ok_or("adapter closure type is missing")?;
    let apparent =
        module.func_type(declaration.func).ok_or("adapter apparent signature is missing")?;
    source_item(input, target)?;
    let body = module.function_by_id(target).ok_or("adapter source target disappeared")?;
    let source_sig = module.func_type(body.ty).ok_or("adapter source signature is missing")?;
    let logical: Vec<_> =
        std::iter::once(if shape.borrowed_zero { Ty::Ptr } else { Ty::Closure(closure) })
            .chain(apparent.params.iter().cloned())
            .collect();
    if source_sig.params != logical
        || source_sig.returns != apparent.returns
        || source_sig.is_vararg
        || source_sig.abi.is_some()
        || body.calling_conv != CallingConv::Rust
    {
        return Err(
            "adapter source body does not have its nominal environment-first signature".into()
        );
    }
    module.validate_closure_layouts().map_err(|e| format!("adapter observed frame: {e}"))?;
    let frame = module
        .closure_layout_descriptor(closure)
        .map_err(|e| format!("adapter observed frame: {e}"))?
        .ok_or("adapter has no observed closure frame")?;
    if shape.borrowed_zero
        && (!declaration.captures.is_empty()
            || frame.size != 0
            || frame.align != 1
            || !frame.capture_offsets.is_empty())
    {
        return Err("borrowed empty adapter lacks its actual zero capture frame".into());
    }
    let owner = input.source_ids.iter().copied().any(|owner| {
        if source_item(input, owner).is_err() {
            return false;
        }
        module.function_by_id(owner).is_some_and(|f| {
            f.blocks.iter().flat_map(|b| &b.body).any(|node| {
                matches!(&node.inst, Inst::MakeClosure { ty, func, captures }
                if *ty == closure && *func == id && captures.len() == declaration.captures.len()
                    && captures.iter().zip(&declaration.captures).all(|(value, ty)|
                        f.typed_value(module, *value).is_some_and(|actual| actual.ty == *ty)))
            })
        })
    });
    if !owner {
        return Err("adapter has no independently conserved selected source constructor".into());
    }
    Ok((closure, target, shape.borrowed_zero))
}

fn unsupported(place: &ParamPlace) -> bool {
    match place {
        ParamPlace::Ignore => true,
        ParamPlace::Scalar(s) => s.ext != AbiExt::None || !matches!(s.slot, Slot::Gpr(_)),
        ParamPlace::Pair(a, b) => {
            [a, b].iter().any(|s| s.ext != AbiExt::None || !matches!(s.slot, Slot::Gpr(_)))
        }
    }
}

/// A modeled placement, or None for a valid adapter whose ABI is not yet in
/// this integer-register fragment. None is left unplaced and therefore Unknown
/// at CER; it never substitutes a guessed scalar ABI for stack/sret/extension.
pub(super) fn derive(
    input: &NativeModuleInput<'_>,
    id: FuncId,
) -> Result<Option<FnPlacement>, String> {
    let (closure, target, borrowed_zero) = protocol(input, id)?;
    let module = input.producer;
    let info = module.target_info.as_ref().ok_or("adapter ABI target is missing")?;
    if info.pointer_size != 8
        || info.endianness != Endianness::Little
        || !(info.triple.starts_with("arm64-apple-macosx")
            || info.triple == "aarch64-apple-darwin"
            || info.triple == "aarch64-unknown-linux-gnu")
    {
        return Ok(None);
    }
    let adapter = module.function_by_id(id).ok_or("adapter function disappeared")?;
    let Some(flat) =
        flat_placement(module.func_type(adapter.ty).ok_or("adapter signature disappeared")?)
    else {
        return Ok(None);
    };
    let body_item = source_item(input, target)?;
    let Some(actual) = &body_item.placement else {
        return Ok(None);
    };
    let declaration = module.closure_type(closure).ok_or("adapter closure type disappeared")?;
    let count = declaration.captures.len();
    if actual.params.len() != flat.params.len() + 1 - count {
        return Err("adapter source placement has the wrong logical parameter count".into());
    }
    if !borrowed_zero && count == 0 {
        // The nominal, by-value empty environment is a logical source parameter,
        // but the actual source ABI passes no bytes and consumes no register.
        // Only that exact leading Ignore may disappear: all apparent arguments
        // and the result must still match the independently selected source ABI.
        let frame = module
            .closure_layout_descriptor(closure)
            .map_err(|e| format!("adapter frame: {e}"))?
            .ok_or("adapter frame disappeared")?;
        if frame.size != 0 || frame.align != 1 || !frame.capture_offsets.is_empty() {
            return Err("owned empty adapter lacks its actual zero capture frame".into());
        }
        if actual.params[0] != ParamPlace::Ignore
            || actual.params[1..] != flat.params
            || actual.ret != flat.ret
        {
            return Err("owned empty adapter differs from the actual source ABI".into());
        }
        return Ok(Some(flat));
    }
    if matches!(actual.ret, ReturnPlace::Indirect)
        || actual.params.iter().any(unsupported)
        || matches!(&actual.ret, ReturnPlace::Scalar(s) if s.ext != AbiExt::None || !matches!(s.slot, Slot::Gpr(_)))
    {
        return Ok(None);
    }
    if actual.ret != flat.ret {
        return Err(
            "adapter compiler-defined return ABI differs from its source body's actual placement"
                .into(),
        );
    }
    let frame = module
        .closure_layout_descriptor(closure)
        .map_err(|e| format!("adapter frame: {e}"))?
        .ok_or("adapter frame disappeared")?;
    let mut size = 0u64;
    let mut align = 1u64;
    for ty in &declaration.captures {
        let Some(bits) = width(ty) else {
            return Ok(None);
        };
        let bytes = u64::from(bits / 8);
        align = align.max(bytes);
        size = size.div_ceil(bytes) * bytes + bytes;
    }
    size = size.div_ceil(align) * align;
    if frame.size != size || frame.align != align {
        return Err("adapter source frame differs from the native scalar carrier totals".into());
    }
    if borrowed_zero {
        // The source's borrowed environment consumes a real pointer register;
        // apparent arguments shift relative to the adapter's capture-free ABI.
        // Compare the actual selected source ABI, never guess that shift from
        // a closure label or silently accept stack/extension carriers.
        let source = module.function_by_id(target).ok_or("source body disappeared")?;
        let Some(expected_source) =
            flat_placement(module.func_type(source.ty).ok_or("source signature disappeared")?)
        else {
            return Ok(None);
        };
        if actual.params != expected_source.params || actual.ret != expected_source.ret {
            return Err("borrowed empty adapter differs from the actual source ABI".into());
        }
        return Ok(Some(flat));
    }
    match (&actual.params[0], declaration.captures.as_slice(), frame.capture_offsets.as_slice()) {
        (ParamPlace::Scalar(s), [ty], [0]) if size <= 8 => {
            if *s != ScalarPlace::gpr(0, width(ty).ok_or("adapter capture width disappeared")?) {
                return Err(
                    "adapter source scalar environment placement differs from its actual capture"
                        .into(),
                );
            }
        }
        (ParamPlace::Pair(a, b), [x, y], [ox, oy]) if size > 8 && size <= 16 => {
            let (rx, ry) = match (*ox, *oy) {
                (0, 8) => (0, 1),
                (8, 0) => (1, 0),
                _ => return Err("adapter source frame is not two observed argument words".into()),
            };
            if *a
                != ScalarPlace::gpr(rx, width(x).ok_or("adapter first capture width disappeared")?)
                || *b
                    != ScalarPlace::gpr(
                        ry,
                        width(y).ok_or("adapter second capture width disappeared")?,
                    )
            {
                return Err(
                    "adapter source pair placement does not follow observed physical offsets"
                        .into(),
                );
            }
        }
        _ => return Ok(None),
    }
    if actual.params[1..] != flat.params[count..] {
        return Err(
            "adapter apparent argument placement differs from its source body's actual ABI".into(),
        );
    }
    Ok(Some(flat))
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "adapter_placement/tests.rs"]
mod tests;
