//! Return-specific fat-pointer metadata facts. This is not generic CHC support.
use trust_types::UnOp;

use super::*;

pub(super) enum MetadataReturnPin {
    NotApplicable,
    Exact(Formula),
    Unsupported(&'static str),
}

/// The selected predecessor and return block describe one return edge, not
/// every predecessor at once. Only its unique whole-return assignment can
/// justify a final-value equality. An unrelated/stale pin cannot repair a
/// declined metadata read on this edge.
pub(super) fn for_return_path(
    func: &VerifiableFunction,
    predecessor: &trust_types::BasicBlock,
    returned: &trust_types::BasicBlock,
) -> MetadataReturnPin {
    use MetadataReturnPin::{Exact, NotApplicable, Unsupported};
    let blocks =
        if predecessor.id == returned.id { vec![returned] } else { vec![predecessor, returned] };
    if !blocks.iter().flat_map(|block| &block.stmts).any(|statement| {
        matches!(statement, Statement::Assign { place, rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, _), .. }
            if place.local == 0)
    }) {
        // An upstream metadata definition must not disappear into the old
        // return-pin fallback merely because a no-op or call separates it from
        // this two-block segment. A direct non-metadata final assignment (the
        // arithmetic arm of A9, for example) remains outside this new lane.
        let has_final_assignment = blocks.iter().flat_map(|block| &block.stmts).any(|statement| {
            matches!(statement, Statement::Assign { place, .. }
                if place.local == 0 && place.projections.is_empty())
        });
        if !has_final_assignment
            && func.body.blocks.iter().flat_map(|block| &block.stmts).any(|statement| {
                matches!(statement, Statement::Assign { place, rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, _), .. }
                    if place.local == 0)
            })
        {
            return Unsupported("metadata return may be defined upstream of the supported return segment");
        }
        return NotApplicable;
    }
    if crate::validate_function(func).is_err()
        || !matches!(returned.terminator, Terminator::Return)
        || func.body.locals.iter().enumerate().any(|(index, decl)| decl.index != index)
        || func.body.blocks.iter().enumerate().any(|(index, block)| block.id.0 != index)
    {
        return Unsupported("metadata return has an invalid typed body or return edge");
    }
    let Some(return_decl) = func.body.locals.first() else {
        return Unsupported("metadata return has no return local");
    };
    if return_decl.ty != func.body.return_ty
        || !(return_decl.ty == Ty::usize()
            || matches!(return_decl.ty, Ty::PtrSizedInt { signed: false }))
    {
        return Unsupported(
            "slice/str metadata return requires the exact unsigned pointer-width destination",
        );
    }

    let mut definition = None;
    for block in &blocks {
        // A call/opaque operation after a statement can overwrite the return
        // value, including through effects absent from a destination field.
        if !matches!(block.terminator.write_effect(), trust_types::WriteEffect::NoValueWrite) {
            return Unsupported("metadata return crosses a value-writing or unmodeled terminator");
        }
        for statement in &block.stmts {
            match statement {
                Statement::Assign { place, rvalue, .. } if place.local == 0 => {
                    if !place.projections.is_empty() || definition.is_some() {
                        return Unsupported(
                            "metadata return does not have one final whole-return assignment on this edge",
                        );
                    }
                    definition = Some(rvalue);
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if place.local == 0 =>
                {
                    return Unsupported("metadata return slot is invalidated on this edge");
                }
                Statement::StorageLive(0) | Statement::StorageDead(0) => {
                    return Unsupported("metadata return slot storage changes on this edge");
                }
                Statement::Assign { .. }
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. } => {}
                other if matches!(other.write_effect(), trust_types::WriteEffect::NoValueWrite) => {
                }
                _ => return Unsupported("metadata return crosses an unmodeled statement effect"),
            }
        }
    }
    let Some(Rvalue::UnaryOp(UnOp::PtrMetadata, operand)) = definition else {
        return Unsupported("the final return definition is not the retained metadata read");
    };
    let (Operand::Copy(source) | Operand::Move(source)) = operand else {
        return Unsupported("metadata return requires a typed whole-parameter pointer operand");
    };
    if !source.projections.is_empty() || source.local == 0 || source.local > func.body.arg_count {
        return Unsupported("metadata return requires a direct whole-parameter pointer identity");
    }
    let crate::PtrMetadataModel::Length(length) = crate::ptr_metadata_model(func, operand) else {
        return Unsupported(
            "return metadata is not a modeled slice/str length; thin-pointer unit and vtables are distinct",
        );
    };
    let source_name = crate::place_to_var_name(func, source);
    let length_name = format!("{source_name}{}", super::super::SLICE_LEN_SUFFIX);
    if length != Formula::Var(length_name.clone(), Sort::Int)
        || func
            .body
            .locals
            .iter()
            .filter(|decl| crate::place_to_var_name(func, &Place::local(decl.index)) == source_name)
            .count()
            != 1
        || func
            .body
            .locals
            .iter()
            .any(|decl| crate::place_to_var_name(func, &Place::local(decl.index)) == length_name)
    {
        return Unsupported("metadata return has ambiguous canonical source/length identity");
    }
    if super::super::v2_slice_metadata_root_can_rebind(func, source.local) {
        return Unsupported(
            "metadata return pointer can be reseated or its pointer local can escape",
        );
    }
    // Return-slot aliases are not ordinary `_0` assignments. Screen their
    // creation over the whole function, even if it precedes this segment.
    // Source storage invalidation likewise cannot preserve an entry value.
    for block in &func.body.blocks {
        for statement in &block.stmts {
            match statement {
                Statement::Assign {
                    rvalue: Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place),
                    ..
                } if place.local == 0 => {
                    return Unsupported("metadata return slot has a mutable/raw alias");
                }
                Statement::StorageLive(local) | Statement::StorageDead(local)
                    if *local == source.local =>
                {
                    return Unsupported("metadata return parameter storage is invalidated");
                }
                other
                    if matches!(
                        other.write_effect(),
                        trust_types::WriteEffect::FailClosedOrBackstopped
                    ) =>
                {
                    return Unsupported(
                        "metadata return has an unaccounted function-wide statement effect",
                    );
                }
                _ => {}
            }
        }
        if matches!(
            block.terminator.write_effect(),
            trust_types::WriteEffect::FailClosedOrBackstopped
        ) {
            return Unsupported("metadata return has an unaccounted function-wide control effect");
        }
    }
    // This whole-function effect check establishes the original parameter
    // length independently of the generic value-version oracle. Element stores
    // can conservatively version the whole pointer there (even with a `pre`
    // sentinel), although they cannot change its metadata. Only this proved
    // stable length may have those redundant epochs unified below.
    Exact(length)
}

/// Collapse only epochs of the exact metadata proven stable above. This is
/// not general SSA normalization: other pointers, scalar values, projections,
/// non-Int terms and bound variables retain their identities. If a quantifier
/// shadows the target name, leave its entire body unchanged to avoid capture.
pub(super) fn normalize_stable_length_epochs(formula: Formula, pin: &MetadataReturnPin) -> Formula {
    let MetadataReturnPin::Exact(Formula::Var(length_name, Sort::Int)) = pin else {
        return formula;
    };
    fn normalize(formula: Formula, length_name: &str, bound: &[Symbol]) -> Formula {
        match formula {
            Formula::Forall(bindings, body) => {
                if bindings.iter().any(|(name, _)| name.as_str() == length_name) {
                    return Formula::Forall(bindings, body);
                }
                let mut scope = bound.to_vec();
                scope.extend(bindings.iter().map(|(name, _)| name.clone()));
                Formula::Forall(bindings, Box::new(normalize(*body, length_name, &scope)))
            }
            Formula::Exists(bindings, body) => {
                if bindings.iter().any(|(name, _)| name.as_str() == length_name) {
                    return Formula::Exists(bindings, body);
                }
                let mut scope = bound.to_vec();
                scope.extend(bindings.iter().map(|(name, _)| name.clone()));
                Formula::Exists(bindings, Box::new(normalize(*body, length_name, &scope)))
            }
            other => {
                if other.var_sort() == Some(&Sort::Int)
                    && let Some(name) = other.var_name()
                    && !bound.iter().any(|binder| binder.as_str() == name)
                    && let Some((base, epoch)) = name.split_once('#')
                    && base == length_name
                    && !epoch.is_empty()
                    && epoch.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
                {
                    return Formula::var(length_name, Sort::Int);
                }
                other.map_children(&mut |child| normalize(child, length_name, bound))
            }
        }
    }
    normalize(formula, length_name, &[])
}
