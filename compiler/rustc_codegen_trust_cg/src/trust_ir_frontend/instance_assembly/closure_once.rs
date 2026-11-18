//! Trust: retain a real empty ClosureOnce inventory item under its own identity.
//!
//! Its implementation already exists as the canonical typed adapter. Matching
//! a symbol is insufficient: bind the actual rustc shim/self type, exact source
//! closure handoff and nominal frame, then require independent conservation.
//! This creates no source definition, module clone, body or proof authority.

use std::collections::BTreeSet;

use super::*;

fn select_adapter(
    module: &Module,
    source: FuncId,
    origin: &trust_ir::ty::TypeOrigin,
    symbol: &str,
    conserved: &BTreeSet<FuncId>,
) -> Result<FuncId, String> {
    module
        .validate_closure_layouts()
        .map_err(|error| format!("ClosureOnce frame table is invalid: {error}"))?;
    if !conserved.contains(&source) {
        return Err("ClosureOnce source body has no independent conservation witness".into());
    }
    let mut frames =
        module.closure_layouts.iter().filter(|row| row.origin.as_ref() == Some(origin));
    let frame = frames.next().ok_or("ClosureOnce source frame is missing")?;
    if frames.next().is_some()
        || frame.size != 0
        || frame.align != 1
        || !frame.capture_offsets.is_empty()
    {
        return Err("ClosureOnce source frame is ambiguous or not empty".into());
    }
    let mut adapters = module.functions.iter().filter(|function| {
        conserved.contains(&function.id)
            && matches!(&function.body_gate,
                Some(BodyGate::Gated { authority, .. })
                if authority == trust_thir_lower::crate_module::TRUST_DIRECT_LANE_AUTHORITY)
            && trust_thir_lower::closure_adapter::inspect(
                function,
                &module.closure_types,
                &module.func_types,
            )
            .is_some_and(|shape| {
                shape.borrowed_zero && shape.closure == frame.closure && shape.body == source
            })
    });
    let adapter = adapters.next().ok_or("ClosureOnce has no conserved canonical typed adapter")?;
    if adapters.next().is_some()
        || adapter.name != symbol
        || module.functions.iter().filter(|function| function.name == symbol).count() != 1
    {
        return Err(
            "ClosureOnce canonical adapter has a different or ambiguous link identity".into()
        );
    }
    Ok(adapter.id)
}

pub(super) fn handoff<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
) -> Result<Option<trust_thir_lower::ExactAssembledBodyForCodegen>, String> {
    let ty::InstanceKind::Shim(ty::ShimKind::ClosureOnce { closure, track_caller, .. }) =
        instance.def
    else {
        return Ok(None);
    };
    // Only the already modeled capture-free Fn borrowing protocol qualifies.
    // Every other shim keeps its original refusal through local_body_def.
    if track_caller || !closure.is_local() || tcx.is_coroutine(closure) {
        return Ok(None);
    }
    let Some(source) = instance.args.first().and_then(|arg| arg.as_type()) else {
        return Err("ClosureOnce shim has no actual receiver type".into());
    };
    let ty::Closure(def, args) = *source.kind() else {
        return Ok(None);
    };
    if def != closure
        || source.has_non_region_param()
        || source.has_non_region_infer()
        || args.as_closure().kind() != ty::ClosureKind::Fn
        || !args.as_closure().upvar_tys().is_empty()
    {
        return Ok(None);
    }
    let expected = ty::Instance::fn_once_adapter_instance(tcx, closure, args);
    if expected != instance || tcx.symbol_name(expected).name != symbol {
        return Err("ClosureOnce shim does not match rustc's exact source adapter instance".into());
    }
    let body = ty::Instance::new_raw(closure, args);
    let body_symbol = tcx.symbol_name(body).name;
    let selected = source_closure_handoff(tcx, body, body_symbol)
        .map_err(|error| error.detail)?
        .ok_or("ClosureOnce source body is not an authenticated closure handoff")?;
    let origin = trust_thir_lower::source_closure_type_origin(tcx, source)
        .ok_or("ClosureOnce source frame has no canonical nominal identity")?;
    let conserved = trust_thir_lower::effect_conservation::conserved_function_ids(tcx.sess)?;
    let func_id = select_adapter(&selected.module, selected.func_id, &origin, symbol, &conserved)?;
    Ok(Some(trust_thir_lower::ExactAssembledBodyForCodegen { module: selected.module, func_id }))
}

// Trust: pure adversarial binding controls, separate from native qualification.
#[cfg(test)]
#[path = "closure_once/tests.rs"]
mod tests;
