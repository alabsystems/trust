//! Exact type-validity premises for bounded scalar-return source fragments.
//!
//! This reconstructs data from the original typed body, not proof authority.
//! Nominal enums remain nominal: no scalar source domain is invented for them.

use std::collections::{BTreeMap, BTreeSet};

use trust_types::{
    CompilerContractValueDomain as Domain, Formula, Rvalue, Sort, Statement, Ty, VerifiableFunction,
};

// Bound and charge descriptor/name walks before the shared enum checker hashes
// names or compares fields. This is only a cost preflight; enum_shape/pure_body
// remain the semantic admission rules.
fn charge_value_type(ty: &Ty, depth: usize) -> Option<()> {
    let bytes = match ty {
        Ty::Bool | Ty::Int { width: 1..=64, .. } => 1,
        Ty::Tuple(fields) if depth < 4 && fields.len() <= 8 => {
            for field in fields {
                charge_value_type(field, depth + 1)?;
            }
            1
        }
        Ty::Adt { name, fields, variants, .. } if fields.len() <= 128 && variants.len() <= 64 => {
            let payloads = variants
                .iter()
                .try_fold(0usize, |n, variant| n.checked_add(variant.fields.len()))?;
            if payloads > 127
                || fields
                    .iter()
                    .any(|(_, ty)| !matches!(ty, Ty::Bool | Ty::Int { width: 1..=64, .. }))
                || variants
                    .iter()
                    .flat_map(|v| &v.fields)
                    .any(|(_, ty)| !matches!(ty, Ty::Bool | Ty::Int { width: 1..=64, .. }))
            {
                return None;
            }
            let mut bytes = name.len();
            for (name, _) in fields {
                bytes = bytes.checked_add(name.len())?;
            }
            for variant in variants {
                bytes = bytes.checked_add(variant.name.len())?;
                for (name, _) in &variant.fields {
                    bytes = bytes.checked_add(name.len())?;
                }
            }
            bytes.checked_mul(32)?.checked_add(fields.len() + variants.len() + payloads)?
        }
        _ => return None,
    };
    (!crate::gen_work::record(bytes)).then_some(())
}

pub(super) fn domains(function: &VerifiableFunction) -> Option<BTreeMap<String, Domain>> {
    let body = &function.body;
    let result_domain = match body.return_ty {
        Ty::Bool => Domain::Bool,
        Ty::Int { width: width @ (8 | 16 | 32 | 64), signed: false } => {
            Domain::MachineInt { width, signed: false }
        }
        _ => return None,
    };
    if !function.spec.requires.is_empty() || !function.spec.invariants.is_empty() {
        return None;
    }
    // No entry domain is reconstructed for the original argument-free fragment.
    // Preserve its scope; the existing body regenerator still validates it.
    if body.arg_count == 0 && body.return_ty == Ty::Bool {
        return (function.preconditions.is_empty() && !body.locals.is_empty())
            .then(|| BTreeMap::from([("_0".to_owned(), Domain::Bool)]));
    }
    if !super::inferred_return::return_dependency_body_within_budget(function) {
        return None;
    }
    let _work = crate::gen_work_scope();
    let _analysis = super::FuncAnalysisScope::enter_if_unbound(function);
    let name_bytes = body
        .locals
        .iter()
        .try_fold(0usize, |n, local| n.checked_add(local.name.as_ref().map_or(0, String::len)))?;
    if crate::gen_work::record(
        name_bytes.checked_mul(32)?.checked_add(body.locals.len() + body.blocks.len())?,
    ) {
        return None;
    }
    if body
        .locals
        .iter()
        .take(body.arg_count + 1)
        .skip(1)
        .any(|formal| matches!(formal.ty, Ty::Adt { .. }))
    {
        for local in &body.locals {
            charge_value_type(&local.ty, 0)?;
        }
    }
    crate::validate_function(function).ok()?;
    if body.return_ty != Ty::Bool {
        // Reuse the exact evaluator used for scalar inferred returns. This is
        // admission data only: the source relation still binds every original
        // authored clause and its complete production VC carrier separately.
        super::inferred_return::scalar_return_equation(function).ok()?;
    }
    let mut result = BTreeMap::from([("_0".to_string(), result_domain)]);
    let mut raw_names: BTreeSet<&str> = BTreeSet::from(["_0"]);
    let mut names = BTreeSet::from(["_0".to_owned()]);
    let mut expected = Vec::new();
    let mut has_enum = false;
    for index in 1..=body.arg_count {
        let formal = body.locals.get(index)?;
        if formal.index != index || formal.name.is_none() {
            return None;
        }
        let raw_name = formal.name.as_deref()?;
        let name = crate::local_var_name(function, formal);
        if raw_name.is_empty() || !raw_names.insert(raw_name) || !names.insert(name.clone()) {
            return None;
        }
        let domain = match &formal.ty {
            Ty::Bool => Some(Domain::Bool),
            Ty::Int { width: width @ (8 | 16 | 32 | 64), signed } => {
                let var = Formula::Var(name.clone(), Sort::Int);
                expected.push(Formula::And(vec![
                    Formula::Ge(
                        Box::new(var.clone()),
                        Box::new(trust_semantics::type_min_formula(*width, *signed)),
                    ),
                    Formula::Le(
                        Box::new(var),
                        Box::new(trust_semantics::type_max_formula(*width, *signed)),
                    ),
                ]));
                Some(Domain::MachineInt { width: *width, signed: *signed })
            }
            ty @ Ty::Adt { name: nominal, .. }
                if !nominal.is_empty() && crate::enum_entry::enum_shape(ty) =>
            {
                has_enum = true;
                None
            }
            _ => return None,
        };
        if let Some(domain) = domain
            && result.insert(name, domain).is_some()
        {
            return None;
        }
    }
    if has_enum {
        // Uses the existing origin/type/call checker, with exactly the candidate
        // callees installed by the public entry. No unknown effect or inactive
        // projection gains a source binder from this validation.
        if !crate::enum_entry::pure_body(function) {
            return None;
        }
        let mut discriminants = BTreeMap::new();
        for block in &body.blocks {
            for statement in &block.stmts {
                if crate::gen_work::record(1) {
                    return None;
                }
                let Statement::Assign { place, rvalue: Rvalue::Discriminant(source), .. } =
                    statement
                else {
                    continue;
                };
                if !place.projections.is_empty() || place.local <= body.arg_count {
                    return None;
                }
                if !matches!(crate::local_defs::unique_value_def(function, place.local), Some(Rvalue::Discriminant(actual)) if actual == source)
                {
                    return None;
                }
                let (origin, _) =
                    crate::enum_entry::discriminant_read_with_origin(function, place, source)?;
                let Ty::Adt { variants, .. } = &body.locals.get(origin.local)?.ty else {
                    return None;
                };
                let destination = body.locals.get(place.local)?;
                if !matches!(destination.ty, Ty::Int { .. }) {
                    return None;
                }
                // Mirror the extractor's exact temp spelling. Collision-safe
                // source/body correspondence and complete certificates remain
                // required independently by the caller.
                // Charge before allocating the destination name or tag carrier.
                let name_bytes = destination.name.as_ref().map_or(24, String::len);
                if crate::gen_work::record(name_bytes.checked_mul(32)?.checked_add(variants.len())?)
                {
                    return None;
                }
                let name = destination.name.clone().unwrap_or_else(|| format!("_{}", place.local));
                if raw_names.contains(name.as_str())
                    || !names.insert(name.clone())
                    || crate::local_var_name(function, destination) != name
                {
                    return None;
                }
                let premise = if let [variant] = variants.as_slice() {
                    Formula::Eq(
                        Box::new(Formula::Var(name.clone(), Sort::Int)),
                        Box::new(Formula::Int(variant.discriminant)),
                    )
                } else {
                    let tags: Vec<_> = variants
                        .iter()
                        .map(|variant| {
                            Formula::Eq(
                                Box::new(Formula::Var(name.clone(), Sort::Int)),
                                Box::new(Formula::Int(variant.discriminant)),
                            )
                        })
                        .collect();
                    Formula::Or(tags)
                };
                if discriminants.insert(place.local, (name, premise)).is_some() {
                    return None;
                }
            }
        }
        expected.extend(discriminants.into_values().map(|(_, premise)| premise));
    }
    if function.preconditions != expected || crate::gen_work_tripped() {
        return None;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    #[test]
    fn entry_work_refusal_returns_no_domain_data_and_restores_budget() {
        let function: trust_types::VerifiableFunction = serde_json::from_str(include_str!("../../../trust-source-contract/tests/fixtures/law-entry/coverage_unwind_is_magnitude_order.json")).unwrap();
        assert!(crate::boolean_source_entry_domains(&function, None).is_some());
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                crate::gen_work::set_test_budget(None);
            }
        }
        let restore = Reset;
        crate::gen_work::set_test_budget(Some(1));
        assert!(crate::boolean_source_entry_domains(&function, None).is_none());
        drop(restore);
        assert!(crate::boolean_source_entry_domains(&function, None).is_some());
    }
}
