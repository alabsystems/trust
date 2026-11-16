//! Choose an identity-preserving native source transport, not an ABI/proof grade.
//!
//! Closure-bearing roots retain their existing fail-closed route. Otherwise an
//! exact checked source image with only the native scalar signature surface may
//! use the same transport. Actual rustc FnAbi agreements, conservation, source
//! identities, dependency census, attributes, targets and the object gate remain
//! mandatory after this choice. A failure there never retries ABI legalization.

use std::collections::BTreeSet;

use trust_ir::function_dependencies::{DependencyNode, DependencyRefusalKind, inspect_function_dependencies};
use trust_ir::{CallingConv, Endianness, FuncId, Inst, Module, Producer, StructPassingPolicy, Ty};

pub(crate) struct NativeRouteInput<'a> {
    pub(crate) producer: &'a Module,
    pub(crate) base: Option<&'a Module>,
    pub(crate) source_ids: &'a BTreeSet<FuncId>,
    pub(crate) roots: &'a BTreeSet<FuncId>,
    pub(crate) has_statics: bool,
    pub(crate) target_triple: &'a str,
    pub(crate) pointer_size: u32,
}

/// This is only the already audited native scalar signature surface. It cannot
/// infer a source type or FnAbi from IR (notably Ptr does not prove a thin Ref).
/// Unsupported signatures retain the existing checked legalized transport,
/// including its Bool-return, wide-scalar and aggregate behavior.
fn primitive(ty: &Ty, fp: bool) -> bool {
    (fp && matches!(ty, Ty::F32 | Ty::F64)) || matches!(
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

pub(crate) fn uses_native_source(input: &NativeRouteInput<'_>) -> bool {
    if has_reachable_closure(input.producer, input.roots.iter().copied()) {
        return true;
    }
    let m = input.producer;
    if input.roots.is_empty()
        || !matches!(input.base, Some(base) if base == m)
        || input.has_statics
        || !m.globals.is_empty()
        || !m.global_asm.is_empty()
        || !m.drop_glue.is_empty()
    {
        return false;
    }
    if !matches!(&m.target_info, Some(target)
        if target.triple == input.target_triple
            && target.pointer_size == input.pointer_size && target.pointer_size == 8
            && target.endianness == Endianness::Little
            && target.abi.is_none()
            && target.struct_passing == StructPassingPolicy::Unclassified)
    {
        return false;
    }
    // Check every signature row, including unused rows: the native transport
    // retains the entire image and cannot authorize an unwitnessed aggregate.
    if m.func_types.iter().enumerate().any(|(index, sig)| {
        if sig.abi.is_some() {
            let owners: Vec<_> = m.functions.iter().filter(|f| f.ty.as_usize() == index).collect();
            return owners.is_empty() || owners.iter().any(|f| !super::foreign_declarations::recorded(m, f.id));
        }
        sig.is_vararg
            || sig.returns.len() > 1
            || !sig.params.iter().chain(&sig.returns)
                .all(|ty| primitive(ty, input.target_triple == "arm64-apple-macosx"))
    }) {
        return false;
    }
    if !input.roots.iter().all(|id| {
        input.source_ids.contains(id) && m.function_by_id(*id).is_some_and(|f| !f.is_declaration())
    }) {
        return false;
    }
    // The existing legalized route prunes bodies outside the selected roots.
    // Do not newly force unrelated stored source bodies through native checks:
    // keep that supported behavior until source-native pruning is qualified.
    let mut reached = BTreeSet::new();
    for root in input.roots {
        let census = inspect_function_dependencies(m, *root);
        if census.refusals().iter().any(|problem| !matches!(problem.kind,
            DependencyRefusalKind::BodylessFunction(id) if super::foreign_declarations::recorded(m, id))) {
            return false;
        }
        reached.extend(census.nodes().iter().filter_map(|node| match node {
            DependencyNode::Function(id) => Some(*id),
            _ => None,
        }));
    }
    if reached != m.functions.iter().map(|f| f.id).collect() {
        return false;
    }
    // Never promote an instance assembler's extra/synthetic body or a foreign
    // declaration into a source instance. Real omitted source dependencies are
    // recovered through the existing HIR/identity/FnAbi path after selection.
    m.functions.iter().all(|f| {
        if f.is_declaration() { return super::foreign_declarations::recorded(m, f.id); }
        f.producer == Some(Producer::TRust)
            && input.source_ids.contains(&f.id)
            && matches!(f.calling_conv, CallingConv::Rust | CallingConv::C)
            && m.func_type(f.ty).is_some()
    })
}

/// Observe runtime constructors reached through the real dependency census.
/// Existing closure routing remains independent of primitive eligibility: a
/// malformed/unsupported closure image must still reach the native refusals.
pub(crate) fn has_reachable_closure(
    module: &Module,
    roots: impl IntoIterator<Item = FuncId>,
) -> bool {
    roots.into_iter().any(|root| {
        inspect_function_dependencies(module, root).nodes().iter().any(|node| {
            let DependencyNode::Function(id) = node else { return false };
            module.function_by_id(*id).is_some_and(|function| {
                function
                    .blocks
                    .iter()
                    .flat_map(|block| &block.body)
                    .any(|node| matches!(node.inst, Inst::MakeClosure { .. }))
            })
        })
    })
}

#[cfg(test)]
#[path = "routing/tests.rs"]
mod tests;
