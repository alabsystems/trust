// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//! Typed entry-value reads for bounded pure enum decision bodies. These are
//! original-body dataflow definitions, never inferred postconditions or proof
//! authority. The same origin walk will bind candidate entry projections.

use trust_types::fx::FxHashSet;
use trust_types::{
    AggregateKind, BinOp, Formula, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction,
};

fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int { width: 1..=64, .. })
}

#[inline]
pub(crate) fn canonical_usize_matches(expected: usize, digits: &str) -> bool {
    if expected < 10 {
        digits.as_bytes() == [b'0' + (expected as u8)]
    } else {
        !digits.starts_with('0')
            && digits.bytes().all(|b| b.is_ascii_digit())
            && digits.parse::<usize>().ok() == Some(expected)
    }
}

fn flat_variant_field_matches(index: usize, flat_name: &str, name: &str) -> bool {
    let Some(rest) = flat_name.strip_prefix("__v") else { return false };
    let Some(rest) = rest.strip_suffix(name) else { return false };
    let Some(idx_str) = rest.strip_suffix('_') else { return false };
    canonical_usize_matches(index, idx_str)
}

pub(crate) fn enum_shape(ty: &Ty) -> bool {
    let Ty::Adt { fields, variants, adt_kind: Some(trust_types::AdtKind::Enum), .. } = ty else {
        return false;
    };
    if variants.is_empty()
        || variants.len() > 64
        || fields.len() > 128
        || variants.iter().map(|v| v.fields.len()).sum::<usize>() + 1 != fields.len()
    {
        return false;
    }
    let Some((tag_name, tag_ty @ Ty::Int { width: 1..=64, .. })) = fields.first() else {
        return false;
    };
    if tag_name != "__tag" || variants.iter().any(|variant| !tag_fits(tag_ty, variant.discriminant))
    {
        return false;
    }
    let mut flat = 1;
    if variants.len() <= 16 {
        for (index, variant) in variants.iter().enumerate() {
            if variants[..index]
                .iter()
                .any(|prev| prev.discriminant == variant.discriminant || prev.name == variant.name)
            {
                return false;
            }
            for (name, ty) in &variant.fields {
                let Some((flat_name, flat_ty)) = fields.get(flat) else {
                    return false;
                };
                if !scalar(ty)
                    || flat_ty != ty
                    || !flat_variant_field_matches(index, flat_name, name)
                {
                    return false;
                }
                flat += 1;
            }
        }
        return flat == fields.len();
    }
    let mut names = FxHashSet::with_capacity_and_hasher(variants.len(), Default::default());
    let mut tags = FxHashSet::with_capacity_and_hasher(variants.len(), Default::default());
    for (index, variant) in variants.iter().enumerate() {
        if !names.insert(variant.name.as_str()) || !tags.insert(variant.discriminant) {
            return false;
        }
        for (name, ty) in &variant.fields {
            let Some((flat_name, flat_ty)) = fields.get(flat) else {
                return false;
            };
            if !scalar(ty) || flat_ty != ty || !flat_variant_field_matches(index, flat_name, name) {
                return false;
            }
            flat += 1;
        }
    }
    flat == fields.len()
}

pub(crate) fn tag_fits(ty: &Ty, tag: i128) -> bool {
    match ty {
        Ty::Int { width: width @ 1..=64, signed: true } => {
            -(1_i128 << (width - 1)) <= tag && tag < (1_i128 << (width - 1))
        }
        Ty::Int { width: width @ 1..=64, signed: false } => 0 <= tag && tag < (1_i128 << width),
        _ => false,
    }
}

fn value_type(ty: &Ty, depth: usize) -> bool {
    scalar(ty)
        || enum_shape(ty)
        || matches!(ty, Ty::Tuple(fields)
        if depth < 4 && fields.len() <= 8 && fields.iter().all(|field| value_type(field, depth + 1)))
}

fn structural(place: &Place) -> bool {
    place
        .projections
        .iter()
        .all(|projection| matches!(projection, Projection::Field(_) | Projection::Downcast(_)))
}

pub(crate) fn has_enum_parameter(function: &VerifiableFunction) -> bool {
    crate::generate::enum_entry_has_enum_parameter_for(function)
}

pub(crate) fn has_enum_parameter_uncached(function: &VerifiableFunction) -> bool {
    function.body.return_ty == Ty::Bool
        && (1..=function.body.arg_count).any(|index| {
            function.body.locals.get(index).is_some_and(|local| {
                local.index == index
                    && matches!(
                        local.ty,
                        Ty::Adt { adt_kind: Some(trust_types::AdtKind::Enum), .. }
                    )
            })
        })
        && crate::return_dependency_body_within_budget(function)
        && (1..=function.body.arg_count).any(|index| {
            function
                .body
                .locals
                .get(index)
                .is_some_and(|local| local.index == index && enum_shape(&local.ty))
        })
}

fn operand(operand: &Operand) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => structural(place),
        Operand::Constant(
            trust_types::ConstValue::Bool(_)
            | trust_types::ConstValue::Int(_)
            | trust_types::ConstValue::Uint(_, 1..=64),
        ) => true,
        _ => false,
    }
}

/// No reference, raw address, effect, drop, user call, opaque input or source
/// assumption may be hidden in an unreachable block. This is a whole-CFG scan.
pub(crate) fn pure_body(function: &VerifiableFunction) -> bool {
    match crate::generate::enum_entry_pure_body_non_call_for(function) {
        Some(result) => result,
        None => function.body.blocks.iter().all(|block| match &block.terminator {
            call @ Terminator::Call { .. } => {
                crate::inferred_return_call_for(function, call).is_some()
            }
            _ => true,
        }),
    }
}

pub(crate) fn pure_body_non_call_uncached(function: &VerifiableFunction) -> Option<bool> {
    if function.body.return_ty != Ty::Bool
        || !crate::return_dependency_body_within_budget(function)
        || function.body.locals.iter().any(|local| !value_type(&local.ty, 0))
    {
        return Some(false);
    }
    let mut has_call = false;
    for block in &function.body.blocks {
        let stmts_ok = block.stmts.iter().all(|statement| match statement {
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Nop
            | Statement::Coverage
            | Statement::ConstEvalCounter => true,
            Statement::Assign { place, rvalue, .. }
                if place.projections.is_empty()
                    && !(1..=function.body.arg_count).contains(&place.local) =>
            {
                match rvalue {
                    Rvalue::Use(value) => operand(value),
                    Rvalue::Discriminant(place) => structural(place),
                    Rvalue::UnaryOp(trust_types::UnOp::Not, value) => operand(value),
                    Rvalue::BinaryOp(
                        BinOp::Eq
                        | BinOp::Ne
                        | BinOp::Lt
                        | BinOp::Le
                        | BinOp::Gt
                        | BinOp::Ge
                        | BinOp::BitAnd
                        | BinOp::BitOr
                        | BinOp::BitXor,
                        lhs,
                        rhs,
                    ) => operand(lhs) && operand(rhs),
                    Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                        operands.iter().all(operand)
                    }
                    Rvalue::Aggregate(AggregateKind::Adt { .. }, _) => {
                        // Exact nominal constructor/type/arity validation is
                        // already shared with inferred-call substitution.
                        immutable_constructor_discriminant(function, place).is_some()
                    }
                    _ => false,
                }
            }
            _ => false,
        });
        if !stmts_ok {
            return Some(false);
        }
        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => {}
            Terminator::SwitchInt { discr, .. } => {
                if !operand(discr) {
                    return Some(false);
                }
            }
            Terminator::Call { .. } => {
                has_call = true;
            }
            _ => return Some(false),
        }
    }
    (!has_call).then_some(true)
}

/// Rebase only an immutable value copy or a typed tuple construction to an
/// immutable enum parameter. No spelling-based alias, deref, cast or layout
/// assumption is used. Unknown definitions and all write/escape channels fail.
pub(crate) fn origin(function: &VerifiableFunction, source: &Place) -> Option<Place> {
    if !structural(source)
        || !has_enum_parameter(function)
        || !crate::place_source_is_stable(function, source.local)
        || !pure_body(function)
    {
        return None;
    }
    let mut place = std::borrow::Cow::Borrowed(source);
    let mut expected_ty = None;
    for _ in 0..16 {
        if !crate::place_source_is_stable(function, place.local) {
            return None;
        }
        if (1..=function.body.arg_count).contains(&place.local) {
            let ty = crate::local_ty_ref(function, place.local)?;
            if !enum_shape(ty) {
                return None;
            }
            let Ty::Adt { variants, .. } = ty else {
                return None;
            };
            let valid = match place.projections.as_slice() {
                [] => true,
                [Projection::Downcast(variant), Projection::Field(field)] => {
                    variants.get(*variant).and_then(|variant| variant.fields.get(*field)).is_some()
                }
                _ => false,
            };
            return valid.then(|| place.into_owned());
        }
        let value = crate::local_defs::unique_value_def(function, place.local)?;
        let (source, remainder) = match value {
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) => {
                (source, &place.projections[..])
            }
            Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                let (Projection::Field(index), remainder) = place.projections.split_first()? else {
                    return None;
                };
                let Ty::Tuple(fields) = crate::local_ty_ref(function, place.local)? else {
                    return None;
                };
                if fields.len() != operands.len() {
                    return None;
                }
                let (Operand::Copy(source) | Operand::Move(source)) = operands.get(*index)? else {
                    return None;
                };
                if crate::place_ty_cow(function, source).as_deref() != fields.get(*index) {
                    return None;
                }
                (source, remainder)
            }
            _ => return None,
        };
        if source.local == place.local || !structural(source) {
            return None;
        }
        let expected = expected_ty.get_or_insert_with(|| crate::place_ty_cow(function, &place));
        if remainder.is_empty() {
            if crate::place_ty_cow(function, source).as_deref() != expected.as_deref() {
                return None;
            }
            place = std::borrow::Cow::Owned(source.clone());
        } else {
            let mut next = source.clone();
            next.projections.extend_from_slice(remainder);
            if crate::place_ty_cow(function, &next).as_deref() != expected.as_deref() {
                return None;
            }
            place = std::borrow::Cow::Owned(next);
        }
    }
    None
}

pub(crate) fn scalar_read(function: &VerifiableFunction, source: &Place) -> Option<Formula> {
    if (1..=function.body.arg_count).contains(&source.local)
        || !structural(source)
        || !has_enum_parameter(function)
    {
        return None;
    }
    let ty = crate::place_ty_cow(function, source)?;
    if !scalar(&ty) {
        return None;
    }
    let origin = origin(function, source)?;
    if origin == *source {
        return None;
    }
    Some(crate::operand_to_formula(function, &Operand::Copy(origin)))
}

pub(crate) fn discriminant_read(
    function: &VerifiableFunction,
    destination: &Place,
    source: &Place,
) -> Option<Formula> {
    discriminant_read_with_origin(function, destination, source).map(|(_, formula)| formula)
}

pub(crate) fn discriminant_read_with_origin(
    function: &VerifiableFunction,
    destination: &Place,
    source: &Place,
) -> Option<(Place, Formula)> {
    let source = origin(function, source)?;
    if !source.projections.is_empty() {
        return None;
    }
    let ty = crate::local_ty_ref(function, source.local)?;
    let Ty::Adt { variants, .. } = ty else {
        return None;
    };
    let destination_ty = crate::place_ty_cow(function, destination)?;
    if !variants.iter().all(|variant| tag_fits(&destination_ty, variant.discriminant)) {
        return None;
    }
    let formula = entry_discriminant(function, &source)?;
    Some((source, formula))
}

/// A payload enum's logical discriminator has a separate channel from every
/// payload projection. In particular, flat `.0` may be the first payload and
/// must never stand for the tag. Fieldless enums retain the existing scalar
/// representation. This is a logical read, not a physical-layout claim.
pub(crate) fn entry_discriminant(function: &VerifiableFunction, source: &Place) -> Option<Formula> {
    let ty = crate::place_ty_cow(function, source)?;
    if !enum_shape(&ty) {
        return None;
    }
    let Ty::Adt { variants, .. } = ty.as_ref() else { return None };
    Some(if variants.iter().all(|variant| variant.fields.is_empty()) {
        crate::operand_to_formula(function, &Operand::Copy(source.clone()))
    } else {
        Formula::Var(
            crate::discriminant_formula_var_name(&crate::place_to_var_name(function, source)),
            trust_types::Sort::Int,
        )
    })
}

/// Recover only the tag of one immutable, unaliased whole-local construction.
/// This never treats payload field zero as a tag or borrows a later source
/// value. A non-constructor or unstable actual keeps its logical read instead.
pub(crate) fn immutable_constructor_discriminant(
    function: &VerifiableFunction,
    source: &Place,
) -> Option<Formula> {
    if !source.projections.is_empty() || crate::local_defs::is_parameter(function, source.local) {
        return None;
    }
    let ty = crate::local_ty_ref(function, source.local)?;
    if !enum_shape(ty) {
        return None;
    }
    let Ty::Adt { name: expected_name, variants, .. } = ty else { return None };
    let Rvalue::Aggregate(AggregateKind::Adt { name, variant, active_field: None, args }, operands) =
        crate::local_defs::unique_value_def(function, source.local)?
    else {
        return None;
    };
    if name != expected_name || args.as_ref().is_some_and(|args| args != expected_name) {
        return None;
    }
    let variant = variants.get(*variant)?;
    if variant.fields.len() != operands.len() {
        return None;
    }
    if !crate::place_source_is_stable(function, source.local)
        || !crate::local_defs::storage_never_aliased(function, source.local)
    {
        return None;
    }
    for ((_, wanted), operand) in variant.fields.iter().zip(operands) {
        let valid = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                structural(place) && crate::place_ty_cow(function, place).as_deref() == Some(wanted)
            }
            Operand::Constant(trust_types::ConstValue::Bool(_)) => *wanted == Ty::Bool,
            Operand::Constant(trust_types::ConstValue::Int(value)) => tag_fits(wanted, *value),
            Operand::Constant(trust_types::ConstValue::Uint(value, width)) => {
                matches!(wanted, Ty::Int { width: expected, .. } if width == expected)
                    && i128::try_from(*value).is_ok_and(|value| tag_fits(wanted, value))
            }
            _ => false,
        };
        if !valid {
            return None;
        }
    }
    Some(Formula::Int(variant.discriminant))
}

/// The complete value origin of an enum call argument. A canonical tag over
/// arbitrary storage is not enough to ground a SAT witness: the same immutable
/// origin must supply its payloads too. Accept only typed whole-local copy
/// chains ending at a true entry parameter or a validated construction.
pub(crate) fn call_argument_origin(
    function: &VerifiableFunction,
    source: &Place,
    expected: &Ty,
) -> Option<Place> {
    let mut current = source;
    for _ in 0..16 {
        if !current.projections.is_empty()
            || crate::local_ty_ref(function, current.local) != Some(expected)
            || !crate::place_source_is_stable(function, current.local)
            || !crate::local_defs::storage_never_aliased(function, current.local)
        {
            return None;
        }
        if (1..=function.body.arg_count).contains(&current.local) {
            return Some(current.clone());
        }
        match crate::local_defs::unique_value_def(function, current.local)? {
            Rvalue::Use(Operand::Copy(origin) | Operand::Move(origin))
                if origin.local != current.local =>
            {
                current = origin;
            }
            Rvalue::Aggregate(..) => {
                immutable_constructor_discriminant(function, current)?;
                return Some(current.clone());
            }
            _ => return None,
        }
    }
    None
}

/// A uniquely defined discriminator of an immutable entry enum has this value
/// at EVERY read, including after joins that drop branch-specific definitions.
/// This uses the same unique-value premise as discriminant CSE, additionally
/// limited to the pure entry-origin fragment above. No parameter destination,
/// alias, second write, effect or unstable source may lend a global equality.
pub(crate) fn global_discriminant_facts(function: &VerifiableFunction) -> Vec<Formula> {
    if !has_enum_parameter(function)
        || !function.body.blocks.iter().any(|block| {
            block.stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    Statement::Assign { place, rvalue: Rvalue::Discriminant(_), .. }
                        if place.projections.is_empty()
                            && !(1..=function.body.arg_count).contains(&place.local)
                )
            })
        })
        || !pure_body(function)
    {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &function.body.blocks {
        for statement in &block.stmts {
            let Statement::Assign {
                place: destination, rvalue: Rvalue::Discriminant(source), ..
            } = statement
            else {
                continue;
            };
            if !destination.projections.is_empty()
                || (1..=function.body.arg_count).contains(&destination.local)
                || !matches!(crate::local_defs::unique_value_def(function, destination.local),
                    Some(Rvalue::Discriminant(actual)) if actual == source)
            {
                continue;
            }
            let Some(entry) = discriminant_read(function, destination, source) else {
                continue;
            };
            let value = crate::operand_to_formula(function, &Operand::Copy(destination.clone()));
            if matches!(&value, Formula::Var(_, trust_types::Sort::Int)) {
                facts.push(Formula::Eq(Box::new(value), Box::new(entry)));
            }
        }
    }
    facts
}
