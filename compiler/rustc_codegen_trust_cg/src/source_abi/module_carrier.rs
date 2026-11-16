//! Native aggregate carriers for an otherwise unchanged source image.
//! Actual rustc FnAbi agreement tokens are checked by the rustc-facing caller.
use std::collections::BTreeSet;

use trust_ir::{FuncId, Module, StructPassingPolicy, Ty};

fn flat(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::Isize
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::Usize
            | Ty::Char
    )
}

pub(super) fn classify(
    source: &Module,
    codegen: &mut Module,
    agreements: &[(&Module, FuncId)],
) -> Result<(), String> {
    let mut checked = BTreeSet::new();
    for (image, id) in agreements {
        if !std::ptr::eq(source, *image) || !checked.insert(*id) {
            return Err(
                "native module ABI witness belongs to another image or repeats a body".into()
            );
        }
    }
    let mut original = codegen.clone();
    for function in &mut original.functions {
        let src = source
            .function_by_id(function.id)
            .ok_or("native ABI copy has a function absent from its source")?;
        function.linkage = src.linkage;
        function.visibility = src.visibility;
    }
    if &original != source {
        return Err(
            "native ABI copy changed source bodies, signatures, identities or evidence".into()
        );
    }
    let info = source.target_info.as_ref().ok_or("native ABI source target is absent")?;
    if info.struct_passing != StructPassingPolicy::Unclassified {
        return Err("native ABI source must retain its original unclassified policy".into());
    }
    for id in &checked {
        if source.function_by_id(*id).is_none_or(|f| f.is_declaration()) {
            return Err("native ABI agreement does not name a stored source body".into());
        }
    }
    // Include indirect/unused signature rows: a module-wide classification must
    // not silently authorize another aggregate signature outside the witnesses.
    for (index, signature) in source.func_types.iter().enumerate() {
        if signature.abi.is_some() {
            let owners: Vec<_> = source.functions.iter().filter(|f| f.ty.as_usize() == index).collect();
            if !owners.is_empty() && owners.iter().all(|f|
                crate::trust_ir_frontend::native_source_module::foreign_declarations::recorded(source, f.id))
            { continue; }
        }
        if signature.params.iter().chain(&signature.returns).all(flat) {
            continue;
        }
        let functions: Vec<_> =
            source.functions.iter().filter(|f| f.ty.as_usize() == index).collect();
        if functions.is_empty() || functions.iter().any(|f| !checked.contains(&f.id)) {
            return Err(format!(
                "native ABI aggregate signature {index} lacks an agreement for every source body"
            ));
        }
    }
    // The caller has already checked every retained source/adapter licence.
    // Only this codegen copy changes; source tables and proof inputs stay exact.
    codegen.target_info.as_mut().ok_or("native ABI codegen target is absent")?.struct_passing =
        StructPassingPolicy::NativeC;
    Ok(())
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "module_carrier/tests.rs"]
mod tests;
