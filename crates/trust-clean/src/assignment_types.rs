//! Projection-aware assignment typing for TrustClean recognizers.
//!
//! Trust MIR is a public, deserializable schema. Rustc emits well-typed assignments,
//! but a diagnostic or certificate entry point can also receive a hand-built body.
//! Recognizers which chase an `Assign` must therefore establish the destination and
//! rvalue types themselves; shape recognition and safety VCs are not a type checker.

use trust_types::{
    AggregateKind, BinOp, CallableKind, ConstValue, DatatypeDefs, Operand, Place, Projection,
    Rvalue, Statement, Ty, UnOp, VerifiableBody,
};

fn ty_eq(a: &Ty, b: &Ty) -> bool {
    a.eq_ignoring_disc_index_safe(b)
}

fn int_like(ty: &Ty) -> Option<(u32, bool)> {
    match ty {
        Ty::Int { width, signed } => Some((*width, *signed)),
        Ty::PtrSizedInt { signed } => Some((64, *signed)),
        _ => None,
    }
}

fn legacy_flattened_payload_name(name: &str) -> Option<(usize, usize)> {
    let (variant, field) = name.strip_prefix("__v")?.split_once('_')?;
    Some((variant.parse().ok()?, field.parse().ok()?))
}

/// Validate the exact payload-bearing enum layout emitted before first-class
/// `VariantDef` metadata existed and recover its observable variant count.
///
/// The canonical representation begins with one signed `__tag`, contains at
/// least one payload slot named `__v{variant}_{field}`, and numbers every
/// payload-bearing variant's fields contiguously from zero.  A missing variant
/// number can represent a nullary variant (for example `Option::None`), so the
/// highest payload-bearing variant determines the minimum observable count.
/// Tag-only enums remain ambiguous and deliberately decline unless the dump's
/// authenticated decoder supplies first-class variants.
fn legacy_flattened_variant_count(fields: &[(String, Ty)]) -> Option<usize> {
    let ((tag_name, tag_ty), payloads) = fields.split_first()?;
    if tag_name != "__tag" || !matches!(tag_ty, Ty::Int { signed: true, .. }) || payloads.is_empty()
    {
        return None;
    }

    let mut positions =
        std::collections::BTreeMap::<usize, std::collections::BTreeSet<usize>>::new();
    let mut names = std::collections::BTreeSet::from([tag_name.as_str()]);
    for (name, _) in payloads {
        if !names.insert(name) {
            return None;
        }
        let (variant, field) = legacy_flattened_payload_name(name)?;
        if !positions.entry(variant).or_default().insert(field) {
            return None;
        }
    }
    if positions.values().any(|fields| !fields.iter().copied().eq(0..fields.len())) {
        return None;
    }
    positions.last_key_value()?.0.checked_add(1)
}

/// Recover the number of variants only when `ty` carries one of Trust MIR's
/// two validated enum representations: first-class variant metadata, or the
/// exact historical flattened layout accepted by the projection type checker.
/// Empty-variant structs, tag-only ADTs, and malformed flattened payload names
/// deliberately return `None`.
///
/// R0: `defs` is the body's out-of-band datatype table. A bare
/// `Ty::Datatype { variants: [] }` marker carries no structure INLINE, so it is
/// resolved through that table — and through nothing else. A marker with no
/// entry declines exactly as it did before the table existed.
pub(crate) fn modeled_enum_variant_count(defs: &DatatypeDefs, ty: &Ty) -> Option<usize> {
    inline_modeled_enum_variant_count(ty).or_else(|| {
        // Additive order: the inline reading above is tried FIRST, so only a
        // marker with no inline structure reaches here. The recorded definition
        // is a WHOLE `Ty` — almost always the flattened `Ty::Adt` — so it is read
        // with the SAME function, one level down. Shallow by construction: the
        // definition's own nested markers are not re-resolved here.
        inline_modeled_enum_variant_count(trust_types::datatype_marker_definition(defs, ty)?)
    })
}

/// [`modeled_enum_variant_count`] against the type's own INLINE structure only.
fn inline_modeled_enum_variant_count(ty: &Ty) -> Option<usize> {
    match ty {
        Ty::Adt { variants, .. } if !variants.is_empty() => Some(variants.len()),
        Ty::Adt { fields, variants, faithful_enum_repr: None, .. } if variants.is_empty() => {
            legacy_flattened_variant_count(fields)
        }
        Ty::Datatype { variants, .. } if !variants.is_empty() => Some(variants.len()),
        _ => None,
    }
}

fn legacy_flattened_variant_fields<'a>(
    fields: &'a [(String, Ty)],
    variant: usize,
) -> Option<Vec<&'a Ty>> {
    if variant >= legacy_flattened_variant_count(fields)? {
        return None;
    }
    let mut selected: Vec<_> = fields
        .iter()
        .filter_map(|(name, ty)| {
            let (field_variant, field) = legacy_flattened_payload_name(name)?;
            (field_variant == variant).then_some((field, ty))
        })
        .collect();
    selected.sort_by_key(|(field, _)| *field);
    Some(selected.into_iter().map(|(_, ty)| ty).collect())
}

/// Recover the discriminant type carried by an exact historical flattened
/// enum. The layout validator above supplies the representation provenance;
/// the tag must additionally match the assignment destination exactly.
fn legacy_discriminant_tag_matches(fields: &[(String, Ty)], expected: &Ty) -> bool {
    legacy_flattened_variant_count(fields).is_some()
        && fields.first().is_some_and(|(_, tag_ty)| ty_eq(tag_ty, expected))
}

/// Recover the element of the exact pre-container-model `Vec<T>` layout used
/// by the checked-in `vec_get` corpus.  The legacy fixture projects an index
/// directly from the structural Vec value; modern rustc MIR reaches the same
/// element through slice/index plumbing.  Requiring the full
/// `Vec { RawVec { Unique { *const T }, usize }, usize }` path prevents a
/// similarly named or partially typed ADT from acquiring index semantics.
fn legacy_vec_element_ty(ty: &Ty) -> Option<Ty> {
    let Ty::Adt { name, fields, variants, faithful_enum_repr, .. } = ty else {
        return None;
    };
    if name != "alloc::vec::Vec" || !variants.is_empty() || faithful_enum_repr.is_some() {
        return None;
    }
    let [(buf_name, raw_vec), (len_name, len_ty)] = fields.as_slice() else {
        return None;
    };
    if buf_name != "buf" || len_name != "len" || !precise_usize_ty(len_ty) {
        return None;
    }
    let Ty::Adt { name, fields, variants, faithful_enum_repr, .. } = raw_vec else {
        return None;
    };
    if name != "alloc::raw_vec::RawVec" || !variants.is_empty() || faithful_enum_repr.is_some() {
        return None;
    }
    let [(ptr_name, unique), (cap_name, cap_ty)] = fields.as_slice() else {
        return None;
    };
    if ptr_name != "ptr" || cap_name != "cap" || !precise_usize_ty(cap_ty) {
        return None;
    }
    let Ty::Adt { name, fields, variants, faithful_enum_repr, .. } = unique else {
        return None;
    };
    if name != "core::ptr::unique::Unique" || !variants.is_empty() || faithful_enum_repr.is_some() {
        return None;
    }
    let [(pointer_name, Ty::RawPtr { mutable: false, pointee })] = fields.as_slice() else {
        return None;
    };
    (pointer_name == "pointer").then(|| pointee.as_ref().clone())
}

fn integer_index_ty(ty: &Ty) -> bool {
    int_like(ty).is_some() || matches!(ty, Ty::Bv(_))
}

fn precise_usize_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { width: 64, signed: false } | Ty::PtrSizedInt { signed: false })
}

fn byte_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { width: 8, signed: false })
}

fn field_ty(defs: &DatatypeDefs, ty: &Ty, variant: Option<usize>, field: usize) -> Option<Ty> {
    // R0: a bare datatype marker carries no field structure inline. Widen it
    // through the body's explicit table first, then run the UNCHANGED match on
    // the result. `resolved_datatype` is the identity on every other shape (and
    // on a marker the table does not define), so no case below can see a value
    // it could not see before.
    let ty = &*trust_types::resolved_datatype(defs, ty);
    match ty {
        Ty::Tuple(fields) => variant.is_none().then(|| fields.get(field).cloned()).flatten(),
        Ty::Adt { fields, variants, faithful_enum_repr, .. } => match variant {
            // A faithful first-class enum uses its active variant's compact field
            // list and requires an explicit Downcast before a payload Field.
            Some(v) if faithful_enum_repr.is_some() => {
                variants.get(v)?.fields.get(field).map(|(_, ty)| ty.clone())
            }
            // Historical enum lowering stores variant payloads in the flattened
            // `fields` view using `__v{variant}_` prefixes.
            Some(v) => {
                legacy_flattened_variant_fields(fields, v)?.get(field).map(|ty| (*ty).clone())
            }
            None if faithful_enum_repr.is_some() && !variants.is_empty() => None,
            // Structs and legacy flattened ADTs retain the canonical plain-field
            // view even when legacy variant metadata is also present.
            None => fields.get(field).map(|(_, ty)| ty.clone()),
        },
        Ty::Datatype { variants, .. } => match variant {
            Some(v) => variants.get(v)?.1.get(field).map(|(_, ty)| ty.clone()),
            None if variants.len() == 1 => variants[0].1.get(field).map(|(_, ty)| ty.clone()),
            None => None,
        },
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            variant.is_none().then(|| upvars.get(field).cloned()).flatten()
        }
        // Clean's certified IEEE carrier exposes the three structural fields
        // used by the historical float corpus.  Reuse its one canonical field
        // decomposition so assignment typing cannot drift from reflection.
        Ty::Float { width } if variant.is_none() => {
            crate::reflect::float_field_tys(*width)?.get(field).cloned()
        }
        _ => None,
    }
}

/// Resolve the type of a MIR place, including the projections a recognizer is
/// about to read or write. Invalid projection chains fail closed.
pub(crate) fn place_type(body: &VerifiableBody, place: &Place) -> Option<Ty> {
    let mut ty = body.locals.get(place.local)?.ty.clone();
    let mut downcast = None;
    for projection in &place.projections {
        match projection {
            Projection::Deref => {
                if downcast.is_some() {
                    return None;
                }
                ty = match ty {
                    Ty::Ref { inner, .. } => *inner,
                    Ty::RawPtr { pointee, .. } => *pointee,
                    _ => return None,
                };
            }
            Projection::Downcast(variant) => {
                if downcast.is_some() {
                    return None;
                }
                // R0, THE DECISIVE SITE. Under markers-everywhere the enum a
                // `Downcast` names is spelled bare EVEN AT THE WALK ROOT, so
                // resolving here is what stops `_6 = &((*_1) as Two).0` becoming
                // untypeable — and the recorded definition is a whole `Ty::Adt`,
                // which the unchanged reading below then handles exactly as it
                // handles an inline one. `resolved_datatype` is the identity on
                // everything that is not a bare marker (and on a marker the table
                // does not define), so no case here can see a value it could not
                // see before.
                let resolved = body.resolved_datatype(&ty);
                let count = match resolved.as_ref() {
                    Ty::Adt { variants, .. } if !variants.is_empty() => variants.len(),
                    Ty::Adt { fields, variants, faithful_enum_repr: None, .. }
                        if variants.is_empty() =>
                    {
                        legacy_flattened_variant_count(fields)?
                    }
                    Ty::Datatype { variants, .. } if !variants.is_empty() => variants.len(),
                    _ => return None,
                };
                if *variant >= count {
                    return None;
                }
                downcast = Some(*variant);
            }
            Projection::Field(field) => {
                ty = field_ty(&body.datatype_defs, &ty, downcast.take(), *field)?;
            }
            Projection::Index(index_local) => {
                if downcast.is_some()
                    || !body.locals.get(*index_local).is_some_and(|l| precise_usize_ty(&l.ty))
                {
                    return None;
                }
                ty = match ty {
                    Ty::Array { elem, .. } | Ty::SymArray { elem, .. } | Ty::Slice { elem } => {
                        *elem
                    }
                    ty @ Ty::Adt { .. } => legacy_vec_element_ty(&ty)?,
                    _ => return None,
                };
            }
            Projection::ConstantIndex { offset, min_length, from_end } => {
                if downcast.is_some() {
                    return None;
                }
                ty = match ty {
                    Ty::Array { elem, len } => {
                        let offset = u64::try_from(*offset).ok()?;
                        let min_length = u64::try_from(*min_length).ok()?;
                        if len < min_length
                            || (!*from_end && offset >= len)
                            || (*from_end && offset == 0)
                            || (*from_end && offset > len)
                        {
                            return None;
                        }
                        *elem
                    }
                    Ty::SymArray { elem, .. } | Ty::Slice { elem } => *elem,
                    _ => return None,
                };
            }
            Projection::Subslice { from, to, from_end } => {
                if downcast.is_some() {
                    return None;
                }
                ty = match ty {
                    Ty::Slice { elem } => Ty::Slice { elem },
                    Ty::Array { elem, len } => {
                        let from = u64::try_from(*from).ok()?;
                        let to = u64::try_from(*to).ok()?;
                        let new_len = if *from_end {
                            len.checked_sub(from)?.checked_sub(to)?
                        } else {
                            if to < from || to > len {
                                return None;
                            }
                            to - from
                        };
                        Ty::Array { elem, len: new_len }
                    }
                    _ => return None,
                };
            }
            Projection::OpaqueCast(projected) | Projection::UnwrapUnsafeBinder(projected) => {
                if downcast.is_some() {
                    return None;
                }
                ty = projected.clone();
            }
            _ => return None,
        }
    }
    downcast.is_none().then_some(ty)
}

fn signed_fits(value: i128, width: u32) -> bool {
    if width >= 128 {
        return true;
    }
    if width == 0 {
        return false;
    }
    let bound = 1_i128 << (width - 1);
    (-bound..bound).contains(&value)
}

fn unsigned_fits(value: u128, width: u32) -> bool {
    width >= 128 || (width > 0 && value < (1_u128 << width))
}

fn string_constant_matches_type(bytes: &[u8], expected: &Ty) -> bool {
    let Ty::Ref { mutable: false, inner } = expected else {
        return false;
    };
    match inner.as_ref() {
        Ty::Str => true,
        Ty::Slice { elem } => byte_ty(elem),
        Ty::Array { elem, len } => byte_ty(elem) && u64::try_from(bytes.len()).ok() == Some(*len),
        _ => false,
    }
}

fn opaque_reference_constant_matches_type(expected: &Ty) -> bool {
    matches!(
        expected,
        Ty::Ref {
            mutable: false,
            inner
        } if matches!(
            inner.as_ref(),
            Ty::Slice { .. }
                | Ty::Array { .. }
                | Ty::SymArray { .. }
                | Ty::Tuple(_)
                | Ty::Adt { .. }
                | Ty::Datatype { .. }
                | Ty::Dynamic { .. }
                | Ty::Str
        )
    )
}

fn unit_variant_reference_matches_type(enum_name: &str, variant: usize, expected: &Ty) -> bool {
    let Ty::Ref { mutable: false, inner } = expected else {
        return false;
    };
    match inner.as_ref() {
        Ty::Adt { name, variants, .. } if name == enum_name => {
            variants.get(variant).is_some_and(|variant| variant.fields.is_empty())
        }
        Ty::Datatype { name, variants } if name == enum_name => {
            variants.get(variant).is_some_and(|(_, fields)| fields.is_empty())
        }
        _ => false,
    }
}

/// Whether a unit-valued MIR constant is an authenticated representation of
/// this ADT. `fields: []`/`variants: []` alone is not enough: that legacy shape
/// also represents bare type parameters and cannot distinguish an empty enum
/// from a unit struct. Keep the bridge closed to the exact compiler-emitted
/// marker type exercised by the record witness until `Ty` carries explicit ZST
/// constructor metadata.
pub(crate) fn is_canonical_unit_marker_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Adt { name, fields, variants, .. }
            if name == "core::marker::PhantomData"
                && fields.is_empty()
                && variants.is_empty()
    )
}

fn constant_matches_type(value: &ConstValue, expected: &Ty) -> bool {
    match value {
        ConstValue::Bool(_) => matches!(expected, Ty::Bool),
        ConstValue::Int(value) => int_like(expected).is_some_and(|(width, signed)| {
            if signed {
                signed_fits(*value, width)
            } else {
                u128::try_from(*value).is_ok_and(|value| unsigned_fits(value, width))
            }
        }),
        ConstValue::Uint(value, width) => match expected {
            Ty::Char => {
                *width == 32 && u32::try_from(*value).ok().and_then(char::from_u32).is_some()
            }
            Ty::Bv(expected_width) => {
                *width == *expected_width && unsigned_fits(*value, *expected_width)
            }
            _ => int_like(expected).is_some_and(|(expected_width, signed)| {
                !signed && *width == expected_width && unsigned_fits(*value, expected_width)
            }),
        },
        ConstValue::Float(_) => matches!(expected, Ty::Float { width: 64 }),
        ConstValue::FloatBits { width, .. } => {
            matches!(expected, Ty::Float { width: expected_width } if width == expected_width)
        }
        ConstValue::Unit => match expected {
            Ty::Unit => true,
            Ty::Tuple(fields) => fields.is_empty(),
            // Trust: RECORD-WITNESS (2026-07-22) — a `ConstValue::Unit` operand also
            // inhabits the canonical `PhantomData<T>` marker:
            // rustc lowers such a marker-field initializer as a Unit-valued (ZST)
            // constant, so a struct-Aggregate row `S { a, PhantomData, b }` type-checks
            // (previously it failed `all_assignments_match`). A generic parameter, user
            // unit struct, or empty enum can share the legacy empty ADT shape, so none of
            // those receive unit authority without explicit constructor metadata.
            Ty::Adt { .. } => is_canonical_unit_marker_ty(expected),
            _ => false,
        },
        ConstValue::OpaqueScalar { width, signed } => int_like(expected) == Some((*width, *signed)),
        ConstValue::ConstParam { width: 1, signed: false, .. } => matches!(expected, Ty::Bool),
        ConstValue::ConstParam { width, signed, .. } => {
            int_like(expected) == Some((*width, *signed))
        }
        ConstValue::CallableItem { def_path, kind, .. } => match (kind, expected) {
            (CallableKind::FnDef, Ty::FnDef { name, .. })
            | (CallableKind::Closure, Ty::Closure { name, .. }) => name == def_path,
            _ => false,
        },
        ConstValue::Str { bytes } => string_constant_matches_type(bytes, expected),
        // The element type is erased, but the schema retains that this is an
        // immutable aggregate reference. Context may establish that much and no
        // scalar claim; the downstream value remains unconstrained.
        ConstValue::OpaqueConst => opaque_reference_constant_matches_type(expected),
        ConstValue::UnitVariantRef { enum_name, variant } => {
            unit_variant_reference_matches_type(enum_name, *variant, expected)
        }
        _ => false,
    }
}

pub(crate) fn operand_matches_type(
    body: &VerifiableBody,
    operand: &Operand,
    expected: &Ty,
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_type(body, place).is_some_and(|actual| ty_eq(&actual, expected))
        }
        Operand::Constant(value) => constant_matches_type(value, expected),
        Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
        _ => false,
    }
}

fn operand_known_type(body: &VerifiableBody, operand: &Operand) -> Option<Ty> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_type(body, place),
        Operand::Constant(ConstValue::Bool(_)) => Some(Ty::Bool),
        Operand::Constant(ConstValue::Uint(_, width)) => {
            Some(Ty::Int { width: *width, signed: false })
        }
        Operand::Constant(ConstValue::Float(_)) => Some(Ty::Float { width: 64 }),
        Operand::Constant(ConstValue::FloatBits { width, .. }) => Some(Ty::Float { width: *width }),
        Operand::Constant(ConstValue::Unit) => Some(Ty::Unit),
        Operand::Constant(ConstValue::ConstParam { width: 1, signed: false, .. }) => Some(Ty::Bool),
        Operand::Constant(ConstValue::OpaqueScalar { width, signed })
        | Operand::Constant(ConstValue::ConstParam { width, signed, .. }) => {
            Some(Ty::Int { width: *width, signed: *signed })
        }
        // `Int` deliberately has no width in the schema. It is checked against a
        // contextual expected type rather than guessed here.
        _ => None,
    }
}

fn operands_compatible(body: &VerifiableBody, lhs: &Operand, rhs: &Operand) -> bool {
    if let Some(lhs_ty) = operand_known_type(body, lhs) {
        return operand_matches_type(body, rhs, &lhs_ty);
    }
    if let Some(rhs_ty) = operand_known_type(body, rhs) {
        return operand_matches_type(body, lhs, &rhs_ty);
    }
    // Two widthless signed literals carry no evidence for one shared Rust type.
    // A destination type cannot provide that missing operand context because
    // comparisons return Bool/Ordering, not their operand type.
    false
}

/// Two schema-level `Int` constants are signed `i128` values whose equality is
/// independent of the concrete signed Rust width, provided a shared width
/// exists. Every pair fits `i128`, so equality/inequality may use that common
/// carrier without guessing a narrower source type. This deliberately excludes
/// ordering, arithmetic, and mixed constant variants, whose result can depend
/// on width or signedness.
fn width_independent_literal_equality(lhs: &Operand, rhs: &Operand) -> bool {
    matches!(
        (lhs, rhs),
        (Operand::Constant(ConstValue::Int(_)), Operand::Constant(ConstValue::Int(_)))
    )
}

fn ordering_type(ty: &Ty) -> bool {
    let Ty::Adt { name, variants, .. } = ty else {
        return false;
    };
    if !matches!(name.as_str(), "cmp::Ordering" | "core::cmp::Ordering" | "std::cmp::Ordering") {
        return false;
    }
    // `VariantDef::discriminant` is DECODED at the extraction boundary, so
    // `Less` is `-1` — the value this predicate was written against. The
    // former `|| (name == "Less" && variant.discriminant == 255)` disjunct
    // tolerated the RAW `repr(i8)` bit pattern that the boundary used to emit;
    // keeping it now would let a stale raw spelling be recognized as `Ordering`
    // while every other lane reads its tag as `-1`, so it is gone with the
    // convention it existed for.
    let expected = [("Less", -1_i128), ("Equal", 0), ("Greater", 1)];
    variants.len() == expected.len()
        && variants.iter().zip(expected).all(|(variant, (name, discriminant))| {
            variant.name == name
                && variant.discriminant == discriminant
                && variant.fields.is_empty()
        })
}

fn binary_matches_type(
    body: &VerifiableBody,
    op: &BinOp,
    lhs: &Operand,
    rhs: &Operand,
    expected: &Ty,
) -> bool {
    match op {
        BinOp::Eq | BinOp::Ne => {
            matches!(expected, Ty::Bool)
                && (operands_compatible(body, lhs, rhs)
                    || width_independent_literal_equality(lhs, rhs))
        }
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            matches!(expected, Ty::Bool) && operands_compatible(body, lhs, rhs)
        }
        BinOp::Cmp => ordering_type(expected) && operands_compatible(body, lhs, rhs),
        BinOp::Shl | BinOp::Shr => {
            operand_matches_type(body, lhs, expected)
                && (operand_known_type(body, rhs).as_ref().is_some_and(integer_index_ty)
                    || matches!(rhs, Operand::Constant(ConstValue::Int(_))))
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor if matches!(expected, Ty::Bool) => {
            operand_matches_type(body, lhs, expected) && operand_matches_type(body, rhs, expected)
        }
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            (int_like(expected).is_some() || matches!(expected, Ty::Bv(_) | Ty::Float { .. }))
                && operand_matches_type(body, lhs, expected)
                && operand_matches_type(body, rhs, expected)
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
            (int_like(expected).is_some() || matches!(expected, Ty::Bv(_)))
                && operand_matches_type(body, lhs, expected)
                && operand_matches_type(body, rhs, expected)
        }
        _ => false,
    }
}

fn metadata_bearing_type(ty: &Ty) -> bool {
    match ty {
        Ty::Slice { .. } | Ty::Str => true,
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
            matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Str)
        }
        _ => false,
    }
}

fn pointer_pointee_coercion(source: &Ty, destination: &Ty) -> bool {
    ty_eq(source, destination)
        || matches!(
            (source, destination),
            (
                Ty::Array { elem: source_elem, .. }
                    | Ty::SymArray { elem: source_elem, .. },
                Ty::Slice { elem: destination_elem }
            ) if ty_eq(source_elem, destination_elem)
        )
}

/// The components of a `trust_mir_extract::faithful_principal_key`, split at the
/// separators that renderer emits.
///
/// The grammar (see `faithful_principal_key`, which is its ONLY producer) is
/// `PATH` optionally followed by `<arg, …>`, then a sorted run of `+[Assoc=Term]`
/// associated-type bindings, then a sorted run of `+AutoTraitPath` auto traits. Every
/// rendered component is bracket-balanced and free of this grammar's metacharacters
/// (`trust_types::key_component_is_unambiguous` / `nominal_path_is_keyable` enforce
/// exactly that, per component, at mint time), so a `+` at bracket depth 0 is always a
/// separator and never part of a component — which is what makes this split well-defined.
struct PrincipalKeyParts<'a> {
    /// Principal trait path plus its non-lifetime arguments — e.g. `krate::Convert<u32>`.
    principal: &'a str,
    /// Associated-type bindings, each the inner text of a `+[…]` group (e.g. `Item=u32`),
    /// in the renderer's sorted order.
    bindings: Vec<&'a str>,
    /// Auto-trait paths, each a trailing `+`-separated segment, in the renderer's sorted
    /// order.
    autos: Vec<&'a str>,
}

/// Split a faithful principal key into [`PrincipalKeyParts`], or `None` if it does not
/// parse in the renderer's grammar.
///
/// FAIL-CLOSED, deliberately: `None` makes the only caller reject the cast. This also
/// declines the historical hand-written multi-bound spelling `"A + B + Send"` (spaces
/// around the separator), which `faithful_principal_key` never emits — refusing to guess
/// at a spelling outside the grammar is preferable to parsing it as an auto-trait list.
fn parse_principal_key(key: &str) -> Option<PrincipalKeyParts<'_>> {
    let mut depth: i32 = 0;
    let mut cuts: Vec<usize> = Vec::new();
    for (i, c) in key.char_indices() {
        match c {
            '(' | '[' | '<' => depth += 1,
            ')' | ']' | '>' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            '+' if depth == 0 => cuts.push(i),
            _ => {}
        }
    }
    if depth != 0 {
        return None;
    }
    let principal = &key[..cuts.first().copied().unwrap_or(key.len())];
    if principal.is_empty() {
        return None;
    }
    let (mut bindings, mut autos) = (Vec::new(), Vec::new());
    for (n, start) in cuts.iter().enumerate() {
        let end = cuts.get(n + 1).copied().unwrap_or(key.len());
        let segment = &key[start + 1..end];
        if let Some(inner) = segment.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            if inner.is_empty() {
                return None;
            }
            bindings.push(inner);
        } else {
            // An auto trait renders as a bare def path: non-empty, no whitespace, no
            // bracket. Anything else is outside the grammar.
            if segment.is_empty()
                || segment.contains(|c: char| c.is_whitespace() || "[]<>()".contains(c))
            {
                return None;
            }
            autos.push(segment);
        }
    }
    Some(PrincipalKeyParts { principal, bindings, autos })
}

/// Whether a raw-pointer pointee cast between two trait objects is reconstructable:
/// principal (path + args + associated-type bindings) EXACTLY equal, auto traits by
/// SUBSET (the destination's must be a subset of the source's).
///
/// # Why not blanket key equality
///
/// Keying this on the erased `trait_name` was loose in the args/bindings direction, but
/// that direction turns out to be INERT BY UPSTREAM ROUTING:
/// `rustc_hir_typeck/src/cast.rs` reconstructs both objects and runs a full `eq` on
/// principal + args + projections, so an args-differing pointer cast is a HARD ERROR at
/// HIR typeck (`tests/ui/cast/ptr-to-trait-obj-different-args.rs`) and never reaches MIR.
///
/// What DOES reach MIR is auto-trait REMOVAL — `*mut (dyn Trait + Send) as *mut dyn Trait`
/// is legal Rust and appears in the `//@ check-pass` file
/// `tests/ui/cast/ptr-to-trait-obj-ok.rs`. Auto traits ARE part of the faithful key, so a
/// blanket key comparison would reject that cast: a pure coverage loss on valid code, and
/// over-rejecting legal Rust is a drop-in-compatibility defect, not a soundness win.
/// Hence subset rather than equality — removal is a legal upcast, ADDITION is not, and
/// rustc likewise rejects addition (`cast.rs`, the "adding an auto trait" arm).
///
/// `None` on either side fails closed: an unrenderable identity cannot be shown equal to
/// anything, and falling back to the erased `trait_name` is the defect this closes.
fn dyn_pointee_cast_compatible(source: Option<&str>, destination: Option<&str>) -> bool {
    let (Some(source), Some(destination)) = (source, destination) else {
        return false;
    };
    let (Some(source), Some(destination)) =
        (parse_principal_key(source), parse_principal_key(destination))
    else {
        return false;
    };
    source.principal == destination.principal
        && source.bindings == destination.bindings
        && destination.autos.iter().all(|auto| source.autos.contains(auto))
}

fn raw_pointer_cast_supported(source: &Ty, destination: &Ty) -> bool {
    match destination {
        // Length-metadata pointers may retain compatible length metadata or be
        // produced by the one reconstructable thin-to-fat unsize coercion.
        Ty::Slice { .. } | Ty::Str => {
            matches!(source, Ty::Slice { .. } | Ty::Str)
                || pointer_pointee_coercion(source, destination)
        }
        // Vtable metadata is identity-bearing; the schema cannot prove trait upcasting or
        // a concrete implementation. Keyed on the FAITHFUL `principal_key`, never the
        // generics-erased `trait_name` — but NOT by blanket equality, because auto-trait
        // removal is legal Rust that reaches MIR. See `dyn_pointee_cast_compatible`.
        Ty::Dynamic { principal_key: destination_key, .. } => {
            matches!(source, Ty::Dynamic { principal_key: source_key, .. }
                if dyn_pointee_cast_compatible(source_key.as_deref(), destination_key.as_deref()))
        }
        Ty::Unsupported { .. } => false,
        // A destination with unit metadata is thin. Rust raw-pointer casts may
        // change its pointee type or discard source metadata.
        _ => !matches!(source, Ty::Unsupported { .. }),
    }
}

fn cast_pair_supported(source: &Ty, destination: &Ty) -> bool {
    if ty_eq(source, destination) {
        return true;
    }
    match (source, destination) {
        (Ty::Bool, destination) | (Ty::Char, destination) => int_like(destination).is_some(),
        (source, destination) if int_like(source).is_some() => {
            int_like(destination).is_some()
                || matches!(destination, Ty::Float { .. } | Ty::RawPtr { .. })
                || (matches!(destination, Ty::Char) && int_like(source) == Some((8, false)))
        }
        (Ty::Float { .. }, destination) => {
            matches!(destination, Ty::Float { .. }) || int_like(destination).is_some()
        }
        (
            Ty::RawPtr { pointee: source_pointee, .. },
            Ty::RawPtr { pointee: destination_pointee, .. },
        ) => raw_pointer_cast_supported(source_pointee, destination_pointee),
        // Trust: ITER-NEXT VALUE-PATH (2026-07-21) — the value-preserving `*T →
        // NonNull<T>` pointer-identity cast, the WRAPPER direction (inverse of the
        // `(Ty::Adt, Ty::RawPtr) => true` transmute below) the slice-iterator cursor
        // snapshot / advance write-back pass through (`_9 = _3 as NonNull`,
        // `_10 = _16 as NonNull`). Checked BEFORE the `(RawPtr, destination)`
        // int-cast catch-all. Category-only, like its inverse — restricted to
        // `NonNull` (NOT arbitrary Adt); the semantic iter lane still applies its own
        // `is_pointerish` provenance proof (`clean_ground::iter_field_root`) before any
        // witness.
        (Ty::RawPtr { .. }, Ty::Adt { name, .. }) if name == "core::ptr::non_null::NonNull" => true,
        (Ty::RawPtr { .. }, destination) => int_like(destination).is_some(),
        (
            Ty::Ref { mutable: source_mutable, inner: source_inner },
            Ty::Ref { mutable: destination_mutable, inner: destination_inner },
        ) => {
            (!*destination_mutable || *source_mutable)
                && pointer_pointee_coercion(source_inner, destination_inner)
        }
        (
            Ty::Ref { mutable: source_mutable, inner: source_inner },
            Ty::RawPtr { mutable: destination_mutable, pointee: destination_pointee },
        ) => {
            (!*destination_mutable || *source_mutable)
                && pointer_pointee_coercion(source_inner, destination_pointee)
        }
        (Ty::FnDef { .. } | Ty::Closure { .. }, Ty::FnPtr { .. }) => true,
        (Ty::FnPtr { .. }, Ty::FnPtr { .. } | Ty::RawPtr { .. }) => true,
        // Extractor-vetted pointer/newtype transmutes retain only the target Ty.
        // This category check does not promote them: every semantic cast lane
        // still applies its more specific proof before producing a witness.
        (Ty::Adt { .. }, Ty::RawPtr { .. }) => true,
        _ => false,
    }
}

fn cast_operand_matches(body: &VerifiableBody, operand: &Operand, destination: &Ty) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_type(body, place).is_some_and(|source| cast_pair_supported(&source, destination))
        }
        Operand::Constant(ConstValue::Bool(_)) => cast_pair_supported(&Ty::Bool, destination),
        // The compatibility schema's widthless signed literal is emitted as i64
        // whenever a cast has no sibling type context.
        Operand::Constant(ConstValue::Int(_)) => {
            cast_pair_supported(&Ty::Int { width: 64, signed: true }, destination)
        }
        Operand::Constant(ConstValue::Uint(_, width)) => {
            cast_pair_supported(&Ty::Int { width: *width, signed: false }, destination)
        }
        Operand::Constant(ConstValue::Float(_)) => {
            cast_pair_supported(&Ty::Float { width: 64 }, destination)
        }
        Operand::Constant(ConstValue::FloatBits { width, .. }) => {
            cast_pair_supported(&Ty::Float { width: *width }, destination)
        }
        Operand::Constant(ConstValue::CallableItem { def_path, kind, .. }) => {
            matches!((kind, destination),
                (CallableKind::FnDef, Ty::FnDef { name, .. })
                    | (CallableKind::Closure, Ty::Closure { name, .. }) if name == def_path)
                || matches!(destination, Ty::FnPtr { .. } | Ty::RawPtr { .. })
        }
        // Type-erased, symbolic, and unsupported operands do not carry enough
        // source-type evidence to certify a cast relation.
        _ => false,
    }
}

fn aggregate_matches_type(
    body: &VerifiableBody,
    kind: &AggregateKind,
    operands: &[Operand],
    expected: &Ty,
) -> bool {
    let matches_fields = |fields: &[Ty]| {
        fields.len() == operands.len()
            && operands
                .iter()
                .zip(fields)
                .all(|(operand, ty)| operand_matches_type(body, operand, ty))
    };
    match (kind, expected) {
        (AggregateKind::Tuple, Ty::Tuple(fields)) => matches_fields(fields),
        (AggregateKind::Tuple, Ty::Unit) => operands.is_empty(),
        (AggregateKind::Array, Ty::Array { elem, len }) => {
            usize::try_from(*len).ok() == Some(operands.len())
                && operands.iter().all(|operand| operand_matches_type(body, operand, elem))
        }
        (AggregateKind::Array, Ty::SymArray { elem, .. }) => {
            operands.iter().all(|operand| operand_matches_type(body, operand, elem))
        }
        (
            AggregateKind::Adt { name, variant, active_field, .. },
            Ty::Adt { name: expected_name, fields, variants, .. },
        ) if name == expected_name => {
            let fields: Vec<Ty> = if variants.is_empty() {
                // Compatibility dumps predating first-class enum variants retain
                // an explicit `__tag` plus flattened `__vN_` payload fields.  The
                // selected aggregate contains only its variant payload, never the
                // tag or the other variants' flattened storage.
                if fields
                    .iter()
                    .any(|(field_name, _)| field_name == "__tag" || field_name.starts_with("__v"))
                {
                    let Some(fields) = legacy_flattened_variant_fields(fields, *variant) else {
                        return false;
                    };
                    fields.into_iter().cloned().collect()
                } else {
                    fields.iter().map(|(_, ty)| ty.clone()).collect()
                }
            } else if let Some(v) = variants.get(*variant) {
                v.fields.iter().map(|(_, ty)| ty.clone()).collect()
            } else {
                return false;
            };
            if let Some(active) = active_field {
                operands.len() == 1
                    && fields
                        .get(*active)
                        .is_some_and(|ty| operand_matches_type(body, &operands[0], ty))
            } else {
                matches_fields(&fields)
            }
        }
        (
            AggregateKind::Adt { name, variant, active_field: None, .. },
            Ty::Datatype { name: expected_name, variants },
        ) if name == expected_name => variants.get(*variant).is_some_and(|(_, fields)| {
            let fields: Vec<Ty> = fields.iter().map(|(_, ty)| ty.clone()).collect();
            matches_fields(&fields)
        }),
        (
            AggregateKind::Closure { name, captures, .. },
            Ty::Closure { name: expected_name, upvars, .. },
        ) if name == expected_name => {
            (captures.is_empty()
                || (captures.len() == upvars.len()
                    && captures.iter().zip(upvars).all(|(a, b)| ty_eq(a, b))))
                && matches_fields(upvars)
        }
        (AggregateKind::Coroutine { name }, Ty::Coroutine { name: expected_name, upvars })
            if name == expected_name =>
        {
            matches_fields(upvars)
        }
        (
            AggregateKind::RawPtr { pointee_ty, mutable },
            Ty::RawPtr { pointee, mutable: expected_mutable },
        ) if mutable == expected_mutable && ty_eq(pointee_ty, pointee) => {
            if operands.len() != 2 {
                return false;
            }
            match pointee_ty {
                Ty::Slice { elem } => {
                    let data_ty = Ty::RawPtr { mutable: *mutable, pointee: elem.clone() };
                    operand_matches_type(body, &operands[0], &data_ty)
                        && operand_known_type(body, &operands[1])
                            .is_some_and(|ty| precise_usize_ty(&ty))
                }
                // These require a vtable/str metadata lane that the assignment
                // checker cannot reconstruct from AggregateKind alone.
                Ty::Dynamic { .. } | Ty::Unsupported { .. } | Ty::Str => false,
                _ => {
                    let data_ty =
                        Ty::RawPtr { mutable: *mutable, pointee: Box::new(pointee_ty.clone()) };
                    operand_matches_type(body, &operands[0], &data_ty)
                        && operand_matches_type(body, &operands[1], &Ty::Unit)
                }
            }
        }
        _ => false,
    }
}

/// Whether `rvalue` can produce exactly `expected`. This is intentionally
/// destination-driven so widthless signed integer literals are checked in their
/// actual MIR context instead of being guessed at an arbitrary width.
pub(crate) fn rvalue_matches_type(body: &VerifiableBody, rvalue: &Rvalue, expected: &Ty) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_matches_type(body, operand, expected),
        Rvalue::BinaryOp(op, lhs, rhs) => binary_matches_type(body, op, lhs, rhs, expected),
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => match expected {
            Ty::Tuple(fields)
                if fields.len() == 2
                    && matches!(fields[1], Ty::Bool)
                    && matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) =>
            {
                binary_matches_type(body, op, lhs, rhs, &fields[0])
            }
            _ => false,
        },
        Rvalue::UnaryOp(UnOp::Not, operand) => {
            (matches!(expected, Ty::Bool) || int_like(expected).is_some())
                && operand_matches_type(body, operand, expected)
        }
        Rvalue::UnaryOp(UnOp::Neg, operand) => {
            (int_like(expected).is_some_and(|(_, signed)| signed)
                || matches!(expected, Ty::Float { .. }))
                && operand_matches_type(body, operand, expected)
        }
        Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
            precise_usize_ty(expected)
                && operand_known_type(body, operand).is_some_and(|ty| metadata_bearing_type(&ty))
        }
        Rvalue::Ref { mutable, place } => match expected {
            Ty::Ref { mutable: expected_mutable, inner } if mutable == expected_mutable => {
                place_type(body, place).is_some_and(|actual| ty_eq(&actual, inner))
            }
            _ => false,
        },
        Rvalue::AddressOf(mutable, place) => match expected {
            Ty::RawPtr { mutable: expected_mutable, pointee } if mutable == expected_mutable => {
                place_type(body, place).is_some_and(|actual| ty_eq(&actual, pointee))
            }
            _ => false,
        },
        Rvalue::Cast(operand, destination) => {
            ty_eq(destination, expected) && cast_operand_matches(body, operand, destination)
        }
        Rvalue::Aggregate(kind, operands) => aggregate_matches_type(body, kind, operands, expected),
        Rvalue::Discriminant(place) => {
            int_like(expected).is_some()
                && place_type(body, place).is_some_and(|ty| {
                    // R0: a discriminant read names the enum by its cut-point
                    // marker under markers-everywhere (in the shipped
                    // `xor_all.json` this is `_2 = Discriminant((*_1))`, on the
                    // ROOT parameter), so widen through the body's EXPLICIT table
                    // before reading the structure. `resolved_datatype` is the
                    // identity on an inline definition and on a marker the table
                    // does not define, so a body that already typed keeps its
                    // exact answer and an unlisted marker still declines.
                    match body.resolved_datatype(&ty).as_ref() {
                        Ty::Adt { fields, variants, faithful_enum_repr, .. } => {
                            !variants.is_empty()
                                || (faithful_enum_repr.is_none()
                                    && legacy_discriminant_tag_matches(fields, expected))
                        }
                        Ty::Datatype { variants, .. } => !variants.is_empty(),
                        _ => false,
                    }
                })
        }
        Rvalue::Len(place) => {
            precise_usize_ty(expected)
                && place_type(body, place).is_some_and(|ty| {
                    matches!(
                        ty,
                        Ty::Array { .. } | Ty::SymArray { .. } | Ty::Slice { .. } | Ty::Str
                    )
                })
        }
        Rvalue::Repeat(operand, count) => match expected {
            Ty::Array { elem, len } => {
                usize::try_from(*len).ok() == Some(*count)
                    && operand_matches_type(body, operand, elem)
            }
            _ => false,
        },
        Rvalue::CopyForDeref(place) => {
            place_type(body, place).is_some_and(|actual| ty_eq(&actual, expected))
        }
        // Trust: W2 reflection — `Rvalue::PtrOffset { ptr, count }` is the extracted
        // `BinOp::Offset`: `ptr.offset(count)` yields a pointer of the SAME raw-pointer
        // type as its base `ptr` (offset preserves provenance/pointee/mutability). This
        // is a PURE type check — it admits the offset assignment as well-typed so the
        // body reaches the recognizers; the pointer's slice-relative VALUE model and its
        // fail-closed in-bounds obligation live in `clean_ground::resolve_ptr_model` /
        // `ptr_offset_bounds_open`, gated at the fully-faithful verdict by
        // `prove::function_ptr_offsets_all_discharged` (an offset that does NOT resolve /
        // discharge keeps the function fail-closed there — never here). The `count`
        // element delta is not type-constrained by the destination.
        Rvalue::PtrOffset { ptr, .. } => {
            matches!(expected, Ty::RawPtr { .. }) && operand_matches_type(body, ptr, expected)
        }
        Rvalue::Unsupported { .. } => false,
        _ => false,
    }
}

/// Check one assignment using the projected destination type.
pub(crate) fn assignment_types_match(
    body: &VerifiableBody,
    place: &Place,
    rvalue: &Rvalue,
) -> bool {
    place_type(body, place)
        .is_some_and(|destination| rvalue_matches_type(body, rvalue, &destination))
}

/// Unwrap a statement only after its assignment type has been established.
pub(crate) fn assigned_rvalue<'a>(
    body: &VerifiableBody,
    statement: &'a Statement,
) -> Option<(&'a Place, &'a Rvalue)> {
    let Statement::Assign { place, rvalue, .. } = statement else {
        return None;
    };
    assignment_types_match(body, place, rvalue).then_some((place, rvalue))
}

/// The common sole-local chase wrapper: require an unprojected assignment to
/// `local` and prove its destination/rvalue type before exposing the rvalue.
pub(crate) fn assigned_local_rvalue<'a>(
    body: &VerifiableBody,
    statement: &'a Statement,
    local: usize,
) -> Option<&'a Rvalue> {
    let (place, rvalue) = assigned_rvalue(body, statement)?;
    (place.local == local && place.projections.is_empty()).then_some(rvalue)
}

/// Whole-body admission check used by certificate entry points. Call-result
/// destinations are terminators rather than `Statement::Assign`; every statement
/// assignment that a later recognizer may chase must be well typed here.
/// Diagnostic re-export of [`assignment_types_match`] so an instrument can locate the
/// offending statement without duplicating the predicate.
#[must_use]
pub(crate) fn assignment_types_match_for_test(
    body: &VerifiableBody,
    place: &Place,
    rvalue: &Rvalue,
) -> bool {
    assignment_types_match(body, place, rvalue)
}

/// Trust: DECLINE LABELLING, ONE LAYER DOWN (2026-08-26) — the OPERAND KIND and the two
/// type spellings that the first failing assignment actually compares.
///
/// The previous instrument reported `operand[0] ty : None`, which its own code returns
/// for a CONSTANT operand — so it distinguished nothing, and the `datatype_defs`
/// hypothesis (that two spellings of one rustc type compare unequal) stayed unconfirmed.
/// This reports the operand KIND explicitly, so "constant" and "place with no computable
/// type" cannot be conflated again.
#[must_use]
pub(crate) fn first_assignment_mismatch_kind(body: &VerifiableBody) -> Option<&'static str> {
    for st in body.blocks.iter().flat_map(|b| &b.stmts) {
        let Statement::Assign { place, rvalue, .. } = st else { continue };
        if assignment_types_match(body, place, rvalue) {
            continue;
        }
        let Some(expected) = place_type(body, place) else {
            return Some("the PLACE has no computable type");
        };
        let Rvalue::Aggregate(kind, operands) = rvalue else {
            // Trust: NON-AGGREGATE SPLIT (2026-08-26) — "non-Aggregate rvalue mismatch" was
            // the single largest decline bucket in the ADT mass (1,159 bodies, 2x
            // over-represented on generics) and as one label it names a dozen unrelated
            // rvalues. Each wants different work, so each gets its own label.
            let place_kind = match &expected {
                Ty::Int { .. } => "Int",
                Ty::Bool => "Bool",
                Ty::Adt { variants, .. } if variants.is_empty() => "struct",
                Ty::Adt { .. } => "enum",
                Ty::Ref { .. } => "Ref",
                Ty::RawPtr { .. } => "RawPtr",
                Ty::Tuple(..) => "Tuple",
                _ => "other",
            };
            return Some(match (rvalue, place_kind) {
                (Rvalue::Use(_), "enum") => "USE into an enum place",
                (Rvalue::Use(_), "struct") => "USE into a struct place",
                (Rvalue::Use(_), _) => "USE into a scalar/other place",
                // Trust: CAST SPLIT (2026-08-26) — 452 bodies, 9x over-represented on
                // generic bodies and the largest generic-specific NON-refusal bucket left
                // after `format!`'s FnPtr was ruled a correct refusal. The cast's declared
                // destination type against the place type is what says whether this is a
                // modelling gap or a coercion the model has no business claiming.
                (Rvalue::Cast(_, dest), _) => {
                    let d = match dest {
                        Ty::Int { .. } => "Int",
                        Ty::Bool => "Bool",
                        Ty::Float { .. } => "Float",
                        Ty::Ref { .. } => "Ref",
                        Ty::RawPtr { .. } => "RawPtr",
                        Ty::Adt { .. } => "Adt",
                        Ty::Slice { .. } => "Slice",
                        Ty::FnPtr { .. } => "FnPtr",
                        Ty::Unsupported { .. } => "Unsupported",
                        _ => "other",
                    };
                    match (d, place_kind) {
                        ("RawPtr", "RawPtr") => "CAST RawPtr -> RawPtr (ptr cast)",
                        ("RawPtr", _) => "CAST to RawPtr into a non-ptr place",
                        ("Ref", _) | (_, "Ref") => "CAST involving a REFERENCE",
                        ("Int", "Int") => "CAST Int -> Int (width/sign)",
                        ("Int", _) => "CAST to Int into a non-Int place",
                        ("Unsupported", _) => "CAST to an UNSUPPORTED destination type",
                        ("Adt", _) | (_, "struct") | (_, "enum") => "CAST involving an ADT",
                        _ => "CAST rvalue mismatch (other)",
                    }
                }
                (Rvalue::Ref { .. }, _) => "REF rvalue mismatch",
                (Rvalue::AddressOf { .. }, _) => "ADDRESS-OF rvalue mismatch",
                (Rvalue::Discriminant(..), _) => "DISCRIMINANT rvalue mismatch",
                (Rvalue::BinaryOp(..) | Rvalue::UncheckedBinaryOp(..), _) => "BINARY-OP mismatch",
                (Rvalue::CheckedBinaryOp(..), _) => "CHECKED-BINARY-OP mismatch",
                (Rvalue::UnaryOp(..), _) => "UNARY-OP mismatch",
                (Rvalue::Len(..), _) => "LEN rvalue mismatch",
                (Rvalue::Repeat(..), _) => "REPEAT rvalue mismatch",
                (Rvalue::CopyForDeref(..), _) => "COPY-FOR-DEREF mismatch",
                (Rvalue::PtrOffset { .. }, _) => "PTR-OFFSET mismatch",
                (Rvalue::Unsupported { .. }, _) => "UNSUPPORTED rvalue (extractor gap)",
                _ => "non-Aggregate rvalue mismatch (unclassified)",
            });
        };
        // Find the operand the aggregate check would reject, and say what it is.
        let fields: Vec<Ty> = match (kind, &expected) {
            (
                AggregateKind::Adt { variant, .. },
                Ty::Adt { fields, variants, .. },
            ) => {
                if let Some(v) = variants.get(usize::try_from(*variant).unwrap_or(usize::MAX)) {
                    v.fields.iter().map(|(_, t)| t.clone()).collect()
                } else {
                    fields.iter().map(|(_, t)| t.clone()).collect()
                }
            }
            (AggregateKind::Tuple, Ty::Tuple(fs)) => fs.clone(),
            _ => return Some("aggregate kind/head does not match the place type"),
        };
        if fields.len() != operands.len() {
            return Some("aggregate ARITY differs from the variant's field count");
        }
        for (op, want) in operands.iter().zip(&fields) {
            if operand_matches_type(body, op, want) {
                continue;
            }
            return Some(match op {
                // Name the CONSTANT kind against the FIELD kind — "a constant does not
                // match" is where the previous layer stopped, and the two halves want
                // different fixes.
                Operand::Constant(c) => {
                    let ck = match c {
                        ConstValue::Int(_) => "Int",
                        ConstValue::Uint(..) => "Uint",
                        ConstValue::Bool(_) => "Bool",
                        ConstValue::Unit => "Unit",
                        ConstValue::Float(_) | ConstValue::FloatBits { .. } => "Float",
                        ConstValue::Str { .. } => "Str",
                        ConstValue::OpaqueConst => "OpaqueConst",
                        _ => "other-const",
                    };
                    let fk = match want {
                        Ty::Int { .. } => "Int",
                        Ty::Bool => "Bool",
                        Ty::Unit => "Unit",
                        Ty::Adt { .. } => "Adt",
                        Ty::Ref { .. } => "Ref",
                        Ty::RawPtr { .. } => "RawPtr",
                        Ty::Tuple(..) => "Tuple",
                        Ty::Float { .. } => "Float",
                        _ => "other-ty",
                    };
                    return Some(match (ck, fk) {
                        ("OpaqueConst", "Adt") => "CONST(OpaqueConst) vs field Adt",
                        ("Str", "Adt") => "CONST(Str) vs field Adt",
                        ("other-const", "Adt") => "CONST(other) vs field Adt",
                        ("OpaqueConst" | "Str" | "other-const", _) => "CONST(non-scalar) vs a non-Adt field",
                        ("Unit", "Adt") => "CONST(Unit) vs field Adt",
                        ("Int" | "Uint", "Adt") => "CONST(Int) vs field Adt",
                        ("Int" | "Uint", "Int") => "CONST(Int) vs field Int (width/sign)",
                        _ => "CONST vs field, other combination",
                    });
                }
                Operand::Copy(place) | Operand::Move(place) => {
                    if place_type(body, place).is_none() {
                        "a PLACE operand has no computable type"
                    } else {
                        "a PLACE operand's type differs from its field type"
                    }
                }
                _ => "an operand of another kind does not match",
            });
        }
        return Some("aggregate mismatch with every operand matching (head/arity)");
    }
    None
}

/// Trust: DECLINE LABELLING (2026-08-26) — which of [`all_assignments_match`]'s four
/// clauses fails. That check stops 56 of the 152 rejected 2-arm-shaped bodies on `fp4`
/// at the recognizer's FIRST gate, which no earlier instrument surfaced, and "a write
/// does not match its place type" was a guess at which clause was responsible.
#[must_use]
pub(crate) fn all_assignments_match_reason(body: &VerifiableBody) -> &'static str {
    if !body.locals.first().is_some_and(|r| ty_eq(&r.ty, &body.return_ty)) {
        return "locals[0].ty != return_ty";
    }
    if body.arg_count >= body.locals.len() {
        return "arg_count >= locals.len()";
    }
    if !body.locals.iter().enumerate().all(|(position, local)| local.index == position) {
        return "local.index does not equal its position";
    }
    if let Some(st) = body.blocks.iter().flat_map(|b| &b.stmts).find(|st| match st {
        Statement::Assign { place, rvalue, .. } => !assignment_types_match(body, place, rvalue),
        _ => false,
    }) {
        // Name the RVALUE KIND that mismatches — this check is a first gate shared by
        // several recognizers, so which shape it rejects matters beyond one lane.
        let Statement::Assign { rvalue, .. } = st else { return "mismatch (unreachable)" };
        return match rvalue {
            Rvalue::Use(..) => "mismatch: Use",
            Rvalue::Aggregate(..) => "mismatch: Aggregate",
            Rvalue::Cast(..) => "mismatch: Cast",
            Rvalue::Ref { .. } => "mismatch: Ref",
            Rvalue::AddressOf(..) => "mismatch: AddressOf",
            Rvalue::BinaryOp(..) => "mismatch: BinaryOp",
            Rvalue::CheckedBinaryOp(..) => "mismatch: CheckedBinaryOp",
            Rvalue::UnaryOp(..) => "mismatch: UnaryOp",
            Rvalue::Discriminant(..) => "mismatch: Discriminant",
            Rvalue::Len(..) => "mismatch: Len",
            _ => "mismatch: other rvalue",
        };
    }
    "all four clauses pass"
}

pub(crate) fn all_assignments_match(body: &VerifiableBody) -> bool {
    body.locals.first().is_some_and(|return_local| ty_eq(&return_local.ty, &body.return_ty))
        && body.arg_count < body.locals.len()
        && body.locals.iter().enumerate().all(|(position, local)| local.index == position)
        && body.blocks.iter().flat_map(|block| &block.stmts).all(|statement| match statement {
            Statement::Assign { place, rvalue, .. } => assignment_types_match(body, place, rvalue),
            _ => true,
        })
}

#[cfg(test)]
mod tests {
    use trust_types::{LocalDecl, VariantDef, VerifiableBody, VerifiableFunction};

    use super::*;

    fn body(locals: Vec<Ty>) -> VerifiableBody {
        VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    #[test]
    fn unit_constant_requires_the_exact_canonical_marker_type() {
        let empty_adt = |name: &str| Ty::adt(name, vec![]);
        assert!(constant_matches_type(&ConstValue::Unit, &empty_adt("core::marker::PhantomData")));
        for forged in ["T", "user::Marker", "user::Never", "user::core::marker::PhantomData"] {
            assert!(
                !constant_matches_type(&ConstValue::Unit, &empty_adt(forged)),
                "empty ADT shape alone must not authorize Unit for `{forged}`"
            );
        }
    }

    #[test]
    fn checked_in_cast_corpus_has_canonical_well_typed_assignments() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures/census-rung2-2026-07-07/cast");
        let mut paths: Vec<_> = std::fs::read_dir(&dir)
            .expect("checked-in cast corpus present")
            .map(|entry| entry.expect("read cast corpus entry").path())
            .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
            .collect();
        paths.sort();

        let mut failures = Vec::new();
        for path in paths {
            let bytes = std::fs::read(&path).expect("read cast fixture");
            let func: VerifiableFunction =
                serde_json::from_slice(&bytes).expect("parse cast fixture");
            let body = &func.body;
            if !body
                .locals
                .first()
                .is_some_and(|return_local| ty_eq(&return_local.ty, &body.return_ty))
                || body.arg_count >= body.locals.len()
                || !body.locals.iter().enumerate().all(|(position, local)| local.index == position)
            {
                failures.push(format!("{}: non-canonical local table", func.def_path));
                continue;
            }
            'blocks: for (block_index, block) in body.blocks.iter().enumerate() {
                for (statement_index, statement) in block.stmts.iter().enumerate() {
                    let Statement::Assign { place, rvalue, .. } = statement else {
                        continue;
                    };
                    if !assignment_types_match(body, place, rvalue) {
                        failures.push(format!(
                            "{}: block {block_index}, statement {statement_index}: \
                             {place:?} = {rvalue:?}",
                            func.def_path,
                        ));
                        break 'blocks;
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "cast corpus contains assignments rejected by the production gate:\n{}",
            failures.join("\n"),
        );
    }

    #[test]
    fn projected_destination_and_deref_source_are_typed() {
        let i32_ty = Ty::Int { width: 32, signed: true };
        let body = body(vec![
            Ty::Tuple(vec![Ty::Bool, i32_ty.clone()]),
            Ty::Ref { mutable: false, inner: Box::new(i32_ty.clone()) },
        ]);
        let destination = Place { local: 0, projections: vec![Projection::Field(1)] };
        let source = Place { local: 1, projections: vec![Projection::Deref] };
        assert!(assignment_types_match(&body, &destination, &Rvalue::Use(Operand::Copy(source))));
    }

    #[test]
    fn bool_from_int_is_rejected_without_needing_an_overflow_vc() {
        let body = body(vec![Ty::Bool]);
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Use(Operand::Constant(ConstValue::Int(0)))
        ));
    }

    #[test]
    fn array_subslice_requires_the_exact_in_bounds_end() {
        let i32_ty = Ty::Int { width: 32, signed: true };
        let body = body(vec![Ty::Array { elem: Box::new(i32_ty.clone()), len: 4 }]);
        let projected = |to| Place {
            local: 0,
            projections: vec![Projection::Subslice { from: 1, to, from_end: false }],
        };
        assert_eq!(
            place_type(&body, &projected(3)),
            Some(Ty::Array { elem: Box::new(i32_ty), len: 2 })
        );
        assert_eq!(place_type(&body, &projected(6)), None);
    }

    #[test]
    fn legacy_adt_and_single_variant_datatype_plain_fields_match_canonical_resolution() {
        let i32_ty = Ty::Int { width: 32, signed: true };
        let variant = VariantDef {
            name: "Only".into(),
            discriminant: 0,
            fields: vec![("0".into(), i32_ty.clone())],
        };
        let legacy = Ty::Adt {
            adt_kind: None,
            layout: None,
            name: "demo::Legacy".into(),
            fields: vec![("__v0_0".into(), i32_ty.clone())],
            variants: vec![variant.clone()],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let first_class = Ty::Adt {
            adt_kind: None,
            layout: None,
            name: "demo::FirstClass".into(),
            fields: vec![("0".into(), i32_ty.clone())],
            variants: vec![variant],
            disc_index_safe: true,
            faithful_enum_repr: Some(None),
            enum_layout: None,
        };
        let datatype = Ty::Datatype {
            name: "demo::Record".into(),
            variants: vec![("mk".into(), vec![("value".into(), i32_ty.clone())])],
        };
        let body = body(vec![legacy, first_class, datatype]);
        assert_eq!(place_type(&body, &Place::field(0, 0)), Some(i32_ty.clone()));
        assert_eq!(place_type(&body, &Place::field(1, 0)), None);
        assert_eq!(place_type(&body, &Place::field(2, 0)), Some(i32_ty));
    }

    #[test]
    fn legacy_payloadless_aggregate_ignores_flattened_variant_storage() {
        let legacy_option = Ty::Adt {
            adt_kind: None,
            layout: None,
            name: "demo::OptionBool".into(),
            fields: vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                ("__v1_0".into(), Ty::Bool),
            ],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let body = body(vec![legacy_option]);
        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "demo::OptionBool".into(),
                    variant: 0,
                    active_field: None,
                    args: None,
                },
                vec![],
            ),
        ));
        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "demo::OptionBool".into(),
                    variant: 1,
                    active_field: None,
                    args: None,
                },
                vec![Operand::Constant(ConstValue::Bool(true))],
            ),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "demo::OptionBool".into(),
                    variant: 99,
                    active_field: None,
                    args: None,
                },
                vec![],
            ),
        ));
    }

    #[test]
    fn legacy_flattened_downcast_requires_one_canonical_payload_layout() {
        let tag = || ("__tag".into(), Ty::Int { width: 64, signed: true });
        let legacy = |fields| Ty::Adt {
            adt_kind: None,
            layout: None,
            name: "demo::OptionPair".into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let valid = legacy(vec![
            tag(),
            ("__v1_0".into(), Ty::Tuple(vec![Ty::Bool, Ty::Int { width: 32, signed: false }])),
        ]);
        let tag_only = legacy(vec![tag()]);
        let missing_zero = legacy(vec![tag(), ("__v1_1".into(), Ty::Bool)]);
        let named_payload = legacy(vec![tag(), ("__v1_value".into(), Ty::Bool)]);
        let tag_after_payload = legacy(vec![("__v1_0".into(), Ty::Bool), tag()]);
        let body = body(vec![valid, tag_only, missing_zero, named_payload, tag_after_payload]);
        let payload = |local| Place {
            local,
            projections: vec![Projection::Downcast(1), Projection::Field(0)],
        };
        assert_eq!(
            place_type(
                &body,
                &Place {
                    local: 0,
                    projections: vec![
                        Projection::Downcast(1),
                        Projection::Field(0),
                        Projection::Field(1),
                    ],
                },
            ),
            Some(Ty::Int { width: 32, signed: false }),
        );
        assert_eq!(
            place_type(
                &body,
                &Place {
                    local: 0,
                    projections: vec![Projection::Downcast(0), Projection::Field(0)],
                },
            ),
            None,
            "the inferred nullary variant has no payload field",
        );
        for local in 1..=4 {
            assert_eq!(
                place_type(&body, &payload(local)),
                None,
                "non-canonical legacy layout local {local} must decline",
            );
        }
    }

    #[test]
    fn tag_only_aggregate_requires_first_class_variant_metadata() {
        let legacy = |name: &str, fields| Ty::Adt {
            adt_kind: None,
            layout: None,
            name: name.into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let exact_tag = || vec![("__tag".into(), Ty::Int { width: 64, signed: true })];
        let first_class_error = Ty::adt_enum(
            "Error",
            (0..4)
                .map(|variant| VariantDef {
                    name: format!("V{variant}"),
                    discriminant: variant,
                    fields: vec![],
                })
                .collect(),
        );
        let body = body(vec![
            first_class_error,
            legacy("Error", exact_tag()),
            legacy("cmp::Ordering", exact_tag()),
            legacy("demo::Error", exact_tag()),
            legacy("cmp::Ordering", vec![("__tag".into(), Ty::Int { width: 32, signed: true })]),
            legacy(
                "Error",
                vec![
                    ("__tag".into(), Ty::Int { width: 64, signed: true }),
                    ("extra".into(), Ty::Unit),
                ],
            ),
        ]);
        let aggregate = |name: &str, variant, active_field, operands| {
            Rvalue::Aggregate(
                AggregateKind::Adt { name: name.into(), variant, active_field, args: None },
                operands,
            )
        };

        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &aggregate("Error", 3, None, vec![]),
        ));
        for (local, name, variant) in [
            (1, "Error", 0),
            (2, "cmp::Ordering", 0),
            (3, "demo::Error", 0),
            (4, "cmp::Ordering", 0),
            (5, "Error", 0),
        ] {
            assert!(
                !assignment_types_match(
                    &body,
                    &Place::local(local),
                    &aggregate(name, variant, None, vec![]),
                ),
                "tag-only aggregate local {local} must decline without first-class variants",
            );
        }
        assert!(!assignment_types_match(
            &body,
            &Place::local(1),
            &aggregate("Error", 0, None, vec![Operand::Constant(ConstValue::Unit)]),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &aggregate("Error", 4, None, vec![]),
        ));
    }

    #[test]
    fn legacy_vec_index_and_structural_float_fields_require_exact_carriers() {
        let u32_ty = Ty::Int { width: 32, signed: false };
        let usize_ty = Ty::Int { width: 64, signed: false };
        let vec_ty = |name: &str, len_ty: Ty, pointer_mutable: bool| {
            Ty::adt(
                name,
                vec![
                    (
                        "buf".into(),
                        Ty::adt(
                            "alloc::raw_vec::RawVec",
                            vec![
                                (
                                    "ptr".into(),
                                    Ty::adt(
                                        "core::ptr::unique::Unique",
                                        vec![(
                                            "pointer".into(),
                                            Ty::RawPtr {
                                                mutable: pointer_mutable,
                                                pointee: Box::new(u32_ty.clone()),
                                            },
                                        )],
                                    ),
                                ),
                                ("cap".into(), usize_ty.clone()),
                            ],
                        ),
                    ),
                    ("len".into(), len_ty),
                ],
            )
        };
        let body = body(vec![
            vec_ty("alloc::vec::Vec", usize_ty.clone(), false),
            usize_ty.clone(),
            vec_ty("demo::Vec", usize_ty.clone(), false),
            vec_ty("alloc::vec::Vec", Ty::Int { width: 64, signed: true }, false),
            vec_ty("alloc::vec::Vec", usize_ty.clone(), true),
            Ty::Float { width: 32 },
        ]);
        let indexed = |local| Place { local, projections: vec![Projection::Index(1)] };

        assert_eq!(place_type(&body, &indexed(0)), Some(u32_ty));
        for local in [2, 3, 4] {
            assert_eq!(place_type(&body, &indexed(local)), None);
        }
        assert_eq!(place_type(&body, &Place::field(5, 0)), Some(Ty::Bool));
        assert_eq!(
            place_type(&body, &Place::field(5, 1)),
            Some(Ty::Int { width: 8, signed: false }),
        );
        assert_eq!(
            place_type(&body, &Place::field(5, 2)),
            Some(Ty::Int { width: 23, signed: false }),
        );
        assert_eq!(place_type(&body, &Place::field(5, 3)), None);
    }

    #[test]
    fn legacy_discriminant_requires_one_exactly_typed_flattened_tag() {
        let discr_ty = Ty::Int { width: 64, signed: true };
        let legacy = |fields| Ty::Adt {
            adt_kind: None,
            layout: None,
            name: "demo::LegacyEither".into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let valid = legacy(vec![
            ("__tag".into(), discr_ty.clone()),
            ("__v0_0".into(), Ty::Unit),
            ("__v1_0".into(), Ty::Bool),
        ]);
        let tag_only = legacy(vec![("__tag".into(), discr_ty.clone())]);
        let wrong_tag_type = legacy(vec![("__tag".into(), Ty::Bool), ("__v0_0".into(), Ty::Unit)]);
        let missing_tag = legacy(vec![("__v0_0".into(), discr_ty.clone())]);
        let duplicate_tag = legacy(vec![
            ("__tag".into(), discr_ty.clone()),
            ("__tag".into(), discr_ty.clone()),
            ("__v0_0".into(), Ty::Unit),
        ]);
        let malformed_payload =
            legacy(vec![("__tag".into(), discr_ty.clone()), ("__vnot-a-variant".into(), Ty::Unit)]);
        let named_payload =
            legacy(vec![("__tag".into(), discr_ty.clone()), ("__v0_payload".into(), Ty::Unit)]);
        let arbitrary_extra_field = legacy(vec![
            ("__tag".into(), discr_ty.clone()),
            ("__v0_0".into(), Ty::Unit),
            ("ordinary_field".into(), Ty::Bool),
        ]);
        let duplicate_payload = legacy(vec![
            ("__tag".into(), discr_ty.clone()),
            ("__v0_0".into(), Ty::Unit),
            ("__v0_0".into(), Ty::Bool),
        ]);
        let body = body(vec![
            discr_ty,
            valid,
            tag_only,
            wrong_tag_type,
            missing_tag,
            duplicate_tag,
            malformed_payload,
            named_payload,
            arbitrary_extra_field,
            duplicate_payload,
        ]);
        let discriminant_of = |local| Rvalue::Discriminant(Place::local(local));

        assert!(assignment_types_match(&body, &Place::local(0), &discriminant_of(1),));
        for local in [2, 3, 4, 5, 6, 7, 8, 9] {
            assert!(
                !assignment_types_match(&body, &Place::local(0), &discriminant_of(local)),
                "legacy discriminant local {local} must fail closed without one exact i64 __tag"
            );
        }
    }

    #[test]
    fn fieldless_ordering_discriminant_requires_first_class_variant_metadata() {
        let i8_ty = Ty::Int { width: 8, signed: true };
        let ordering = |name: &str, fields| Ty::Adt {
            adt_kind: None,
            layout: None,
            name: name.into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let exact_fields = || vec![("__tag".into(), Ty::Int { width: 64, signed: true })];
        let first_class = Ty::adt_enum(
            "cmp::Ordering",
            vec![
                VariantDef { name: "Less".into(), discriminant: -1, fields: vec![] },
                VariantDef { name: "Equal".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "Greater".into(), discriminant: 1, fields: vec![] },
            ],
        );
        let body = body(vec![
            i8_ty.clone(),
            first_class,
            ordering("cmp::Ordering", exact_fields()),
            ordering("user::cmp::Ordering", exact_fields()),
            ordering("cmp::Ordering", vec![("__tag".into(), Ty::Int { width: 32, signed: true })]),
            ordering("cmp::Ordering", vec![("__tag".into(), Ty::Int { width: 64, signed: false })]),
            ordering(
                "cmp::Ordering",
                vec![
                    ("__tag".into(), Ty::Int { width: 64, signed: true }),
                    ("extra".into(), Ty::Unit),
                ],
            ),
            Ty::Int { width: 16, signed: true },
            ordering("cmp::Ordering", exact_fields()),
        ]);
        let discriminant_of = |local| Rvalue::Discriminant(Place::local(local));
        let compare_i8 = || {
            Rvalue::BinaryOp(
                BinOp::Cmp,
                Operand::Copy(Place::local(0)),
                Operand::Copy(Place::local(0)),
            )
        };

        assert!(assignment_types_match(&body, &Place::local(0), &discriminant_of(1)));
        assert!(assignment_types_match(&body, &Place::local(1), &compare_i8()));
        assert!(
            !assignment_types_match(
                &body,
                &Place::local(1),
                &Rvalue::BinaryOp(
                    BinOp::Cmp,
                    Operand::Constant(ConstValue::Int(0)),
                    Operand::Constant(ConstValue::Int(1)),
                ),
            ),
            "literal equality compatibility must not extend to three-way comparison"
        );
        for local in [2, 3, 4, 5, 6] {
            assert!(
                !assignment_types_match(&body, &Place::local(0), &discriminant_of(local)),
                "fieldless Ordering local {local} must decline without first-class variants"
            );
        }
        assert!(
            !assignment_types_match(&body, &Place::local(2), &compare_i8()),
            "tag-only Ordering must not type a comparison result without first-class variants"
        );
        assert!(
            !assignment_types_match(&body, &Place::local(7), &discriminant_of(8)),
            "tag-only Ordering must not admit a non-i8 destination"
        );
    }

    #[test]
    fn index_and_pointer_metadata_require_precise_usize_and_fat_shapes() {
        let u8_ty = Ty::Int { width: 8, signed: false };
        let usize_ty = Ty::Int { width: 64, signed: false };
        let i32_ty = Ty::Int { width: 32, signed: true };
        let slice_ref = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice { elem: Box::new(u8_ty.clone()) }),
        };
        let thin_ref = Ty::Ref { mutable: false, inner: Box::new(i32_ty.clone()) };
        let symbolic_array_ref = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::SymArray {
                elem: Box::new(u8_ty.clone()),
                len_sym: trust_types::ConstLen { index: 0, name: "N".into() },
            }),
        };
        let body = body(vec![
            usize_ty.clone(),
            Ty::Array { elem: Box::new(u8_ty), len: 2 },
            usize_ty,
            i32_ty,
            slice_ref,
            thin_ref,
            symbolic_array_ref,
        ]);
        assert!(
            place_type(&body, &Place { local: 1, projections: vec![Projection::Index(2)] })
                .is_some()
        );
        assert_eq!(
            place_type(&body, &Place { local: 1, projections: vec![Projection::Index(3)] }),
            None
        );
        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(4)))
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(5)))
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(6)))
        ));
    }

    #[test]
    fn raw_pointer_aggregate_and_cast_sources_are_not_shape_only() {
        let i32_ty = Ty::Int { width: 32, signed: true };
        let raw = Ty::RawPtr { mutable: false, pointee: Box::new(i32_ty.clone()) };
        let fat_raw = Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Slice { elem: Box::new(i32_ty.clone()) }),
        };
        let body = body(vec![
            raw.clone(),
            raw.clone(),
            Ty::Bool,
            Ty::Float { width: 64 },
            fat_raw.clone(),
        ]);
        let kind = AggregateKind::RawPtr { pointee_ty: i32_ty, mutable: false };
        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Aggregate(
                kind.clone(),
                vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Unit),],
            )
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Aggregate(kind, vec![Operand::Copy(Place::local(1))])
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(3),
            &Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::Float { width: 64 })
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(4),
            &Rvalue::Cast(Operand::Copy(Place::local(1)), fat_raw),
        ));
    }

    #[test]
    fn semantic_categories_do_not_erase_source_identity() {
        let i32_ty = Ty::Int { width: 32, signed: true };
        let bool_ref = Ty::Ref { mutable: false, inner: Box::new(Ty::Bool) };
        let i32_ref = Ty::Ref { mutable: false, inner: Box::new(i32_ty.clone()) };
        let fake_ordering = Ty::Adt {
            adt_kind: None,
            layout: None,
            name: "user::Ordering".into(),
            fields: vec![("__tag".into(), Ty::Int { width: 64, signed: true })],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        let closure = Ty::Closure { name: "demo::call".into(), upvars: vec![], call: None };
        let body = body(vec![
            Ty::Bool,
            fake_ordering,
            bool_ref.clone(),
            i32_ref,
            i32_ty.clone(),
            i32_ty,
            closure,
        ]);

        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Constant(ConstValue::Int(0)),
                Operand::Constant(ConstValue::Int(0)),
            ),
        ));
        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::BinaryOp(
                BinOp::Ne,
                Operand::Constant(ConstValue::Int(i128::MIN)),
                Operand::Constant(ConstValue::Int(0)),
            ),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Constant(ConstValue::Int(0)),
                Operand::Constant(ConstValue::Int(1)),
            ),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Constant(ConstValue::Int(-1)),
                Operand::Constant(ConstValue::Uint(0, 32)),
            ),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Constant(ConstValue::Int(0)),
                Operand::Constant(ConstValue::Int(1)),
            ),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(1),
            &Rvalue::BinaryOp(
                BinOp::Cmp,
                Operand::Copy(Place::local(4)),
                Operand::Copy(Place::local(5)),
            ),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(2),
            &Rvalue::Cast(Operand::Copy(Place::local(3)), bool_ref),
        ));
        assert!(!assignment_types_match(
            &body,
            &Place::local(6),
            &Rvalue::Use(Operand::Constant(ConstValue::CallableItem {
                def_path: "demo::call".into(),
                kind: CallableKind::FnDef,
                def_path_hash: trust_types::CallableDefPathHash::new(1, 2),
            })),
        ));
    }

    #[test]
    fn whole_body_gate_requires_a_canonical_local_table_and_return_slot() {
        let canonical = body(vec![Ty::Unit]);
        assert!(all_assignments_match(&canonical));

        let mut wrong_index = canonical.clone();
        wrong_index.locals[0].index = 1;
        assert!(!all_assignments_match(&wrong_index));

        let mut wrong_return = canonical.clone();
        wrong_return.return_ty = Ty::Bool;
        assert!(!all_assignments_match(&wrong_return));

        let mut missing_argument_slot = canonical.clone();
        missing_argument_slot.arg_count = 1;
        assert!(!all_assignments_match(&missing_argument_slot));

        let mut missing_return_slot = canonical;
        missing_return_slot.locals.clear();
        assert!(!all_assignments_match(&missing_return_slot));
    }

    /// R0 CRUX — the "identity-bearing marker everywhere" repair for the
    /// canonical-cut root dependence is refuted HERE, by a consumer, not by the
    /// cost of a carrier.
    ///
    /// R0 (`trust-mir-extract::ty_convert`, the `TyKind::Adt` arm) is that a
    /// canonical cut point `C` is emitted as its FULL DEFINITION at the outermost
    /// nominal position of a `convert_ty` walk — the `!ctx.adt_stack.is_empty()`
    /// conjunct — and as a bare `Ty::Datatype { name, variants: [] }` marker
    /// everywhere else, so one rustc type reaches a dump as several `ty_eq`-
    /// unequal values and `all_assignments_match` declines a well-typed body.
    ///
    /// The proposed repair is to DELETE that conjunct so `C` is a marker at every
    /// occurrence, on the theory that if the marker's name is identity-bearing
    /// then equality is exact and nothing ever needs to resolve a marker back to
    /// its variants. Something does need to: `place_type` below.
    /// `Projection::Downcast(v)` has no interpretation without a variant list, so
    /// a markers-everywhere body cannot type `((*_1) as Two).0` — the very
    /// statement R0 makes decline. The deletion trades a decline-because-two-
    /// spellings-disagree for a decline-because-there-is-no-structure-anywhere,
    /// which removes the capability instead of restoring it. Identity is not
    /// enough: the definition has to live SOMEWHERE, so the out-of-band carrier
    /// question the repair was meant to avoid is unavoidable.
    #[test]
    fn a_canonical_cut_marker_at_the_walk_root_cannot_type_a_downcast() {
        let i64_ty = || Ty::Int { width: 64, signed: true };
        // `Tree`'s recursive children are `Arc<Tree>`; the Arc subtree's exact
        // shape is irrelevant here, only that the variant list exists at all.
        let arc = || Ty::Datatype { name: "std::sync::Arc".into(), variants: vec![] };
        let variant = |name: &str, discriminant: i128, fields: Vec<(String, Ty)>| VariantDef {
            name: name.into(),
            discriminant,
            fields,
        };

        // `Tree` as the producer lowers it at a walk's outermost nominal position
        // today: the flattened `__tag` / `__v{v}_{f}` view plus first-class
        // variants. Shape taken from the shipped
        // `fixtures/structural-fold-corpus/xor_all.json`, `locals[1].ty`.
        let tree_definition = Ty::Adt {
            name: "Tree".into(),
            fields: vec![
                ("__tag".into(), i64_ty()),
                ("__v0_0".into(), i64_ty()),
                ("__v1_0".into(), arc()),
                ("__v2_0".into(), arc()),
                ("__v2_1".into(), arc()),
            ],
            variants: vec![
                variant("Leaf", 0, vec![("0".into(), i64_ty())]),
                variant("One", 1, vec![("0".into(), arc())]),
                variant("Two", 2, vec![("0".into(), arc()), ("1".into(), arc())]),
            ],
            disc_index_safe: true,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: None,
        };
        // The identity-bearing marker `canonical_cut_ref` emits for the SAME rustc
        // type. `Tree` takes no non-lifetime generic argument, so the marker
        // carries the erased def path — already the most identity it can carry.
        let tree_marker = Ty::Datatype { name: "Tree".into(), variants: vec![] };

        // `_6 = &((*_1) as Two).0`, the shipped declining statement.
        let two_field_0 = Place {
            local: 1,
            projections: vec![Projection::Deref, Projection::Downcast(2), Projection::Field(0)],
        };

        let with_root_definition =
            body(vec![Ty::Unit, Ty::Ref { mutable: false, inner: Box::new(tree_definition) }]);
        assert_eq!(
            place_type(&with_root_definition, &two_field_0),
            Some(arc()),
            "a cut point that keeps its definition at the walk root types the downcast",
        );

        let markers_everywhere =
            body(vec![Ty::Unit, Ty::Ref { mutable: false, inner: Box::new(tree_marker.clone()) }]);
        assert_eq!(
            place_type(&markers_everywhere, &two_field_0),
            None,
            "deleting the root conjunct leaves `Downcast(2)` no variant list to \
             resolve, so the identity-marker design cannot stand alone — it needs \
             an out-of-band definition carrier",
        );
        assert_eq!(
            modeled_enum_variant_count(&DatatypeDefs::new(), &tree_marker),
            None,
            "a bare marker carries no variant count, however identity-bearing its name",
        );
    }

    /// The companion no-over-merge pins for the same design. Over-merging two
    /// distinct types is worse than R0's fail-closed decline, so a marker must
    /// stay UNEQUAL to a marker for any other type, and — because the canonical
    /// cut is only ONE of three producers of the `Ty::Datatype { name, variants:
    /// [] }` shape — no consumer may resolve a marker by name at all.
    ///
    /// The other two producers, both in `trust-mir-extract::ty_convert`:
    ///   * the legacy `adt_stack` back-edge guard (`recursive_datatype_ref(&name)`
    ///     in the struct arm, `datatype_child_field_ty`, `lower_adt_as_datatype`
    ///     and `lower_enum_adt`), which uses the GENERICS-ERASED def path; and
    ///   * `compact_oversized_field`, which emits the same shape for ANY oversized
    ///     nested ADT field purely to bound tree size — also erased, and not a
    ///     back-edge at all.
    /// `canonical_cut_ref` renders the instantiated path only when the type has a
    /// non-lifetime generic argument, so for a NON-generic cut point its marker is
    /// byte-identical to both of the others. Name resolution therefore cannot tell
    /// a real cut from a compacted `Big<u8>` field, which is exactly how the
    /// withdrawn consumer-side repair failed open.
    #[test]
    fn cut_point_markers_stay_distinct_and_are_never_resolved_by_name() {
        let marker = |name: &str| Ty::Datatype { name: name.into(), variants: vec![] };

        // Two instantiations of one generic cut point stay distinct: a generic cut
        // point's marker carries the fully-instantiated def path.
        assert!(
            !ty_eq(
                &marker("krate::Foo<std::vec::Vec<u8>>"),
                &marker("krate::Foo<std::vec::Vec<i32>>"),
            ),
            "`Foo<Vec<u8>>` and `Foo<Vec<i32>>` are two cut points and must not merge",
        );

        // Two distinct cycles whose types share a leaf name stay distinct: the def
        // path is rendered untrimmed, so the module prefix survives.
        assert!(
            !ty_eq(&marker("krate::alpha::Node"), &marker("krate::beta::Node")),
            "two same-named recursive types in different modules must not merge",
        );

        // A cut point and an unrelated compacted aggregate stay distinct.
        assert!(!ty_eq(&marker("krate::Big"), &marker("__trust_compacted_aggregate")));

        // The fail-CLOSED half. For a non-generic name the three producers are
        // byte-identical, so every consumer must decline on a bare marker rather
        // than bind it to a definition found elsewhere. Pin that both variant
        // readers in this module do decline, for a real cut name, a generic cut
        // name, and `compact_oversized_field`'s fallback name alike.
        for name in ["krate::Big", "krate::Foo<std::vec::Vec<u8>>", "__trust_compacted_aggregate"] {
            assert_eq!(
                modeled_enum_variant_count(&DatatypeDefs::new(), &marker(name)),
                None,
                "a bare `{name}` marker must not yield a variant count",
            );
            assert_eq!(
                place_type(
                    &body(vec![Ty::Unit, marker(name)]),
                    &Place { local: 1, projections: vec![Projection::Downcast(0)] },
                ),
                None,
                "a bare `{name}` marker must not admit a downcast",
            );
        }
    }

    /// R0 REPAIR — the consumer half. The two tests above pin that a bare marker
    /// carries no structure and that no consumer may go LOOKING for it. This one
    /// pins the sanctioned way the structure comes back: an EXPLICIT out-of-band
    /// entry on the body itself (`VerifiableBody::datatype_defs`).
    ///
    /// All four halves are asserted together, in one test, on purpose — each is
    /// the failure mode of the other three, so splitting them would let a future
    /// edit "fix" one by breaking one of the others:
    ///
    ///   1. a marker WITH a matching entry resolves — the capability restored;
    ///   2. a marker with NO entry still declines — fail-closed preserved, and
    ///      this is what makes the widening additive rather than a rewrite;
    ///   3. an entry under a DIFFERENT name does not bind — resolution is a keyed
    ///      lookup, never a scan of whatever definitions happen to be in scope;
    ///   4. `Foo<Vec<u8>>` and `Foo<Vec<i32>>` stay unequal AND stay unresolvable
    ///      from each other's entry — the exact fail-OPEN that sank the withdrawn
    ///      by-name-body-search repair is a failing assertion here.
    #[test]
    fn a_bare_cut_marker_resolves_only_through_an_explicit_table_entry() {
        let i64_ty = || Ty::Int { width: 64, signed: true };
        let arc = || Ty::Datatype { name: "std::sync::Arc".into(), variants: vec![] };
        let marker = |name: &str| Ty::Datatype { name: name.into(), variants: vec![] };

        // `Tree`'s definition as the TABLE carries it. TWO shapes are pinned,
        // because the widened carrier holds a whole `Ty` and the producer emits
        // BOTH: `lower_adt_as_datatype` yields a `Ty::Datatype` (the Lever A
        // `Level`/`Expr`/`ExprKind` cluster) while every other recursive ADT —
        // `Tree` included — goes through `lower_enum_adt` and yields a `Ty::Adt`
        // with real discriminants and the flat `__v{v}_{f}` view. The `Ty::Adt`
        // shape is the one that occurs 7855 times in the shipped corpus and 0
        // times in the narrow carrier's value type.
        let tree_variants: trust_types::DatatypeVariants = vec![
            ("Leaf".into(), vec![("0".into(), i64_ty())]),
            ("One".into(), vec![("0".into(), arc())]),
            ("Two".into(), vec![("0".into(), arc()), ("1".into(), arc())]),
        ];
        let tree_datatype_def =
            Ty::Datatype { name: "Tree".into(), variants: tree_variants.clone() };
        // The `lower_enum_adt` spelling of the SAME type, taken from the shipped
        // `fixtures/structural-fold-corpus/xor_all.json` `locals[1].ty`.
        let tree_adt_def = Ty::Adt {
            name: "Tree".into(),
            fields: vec![
                ("__tag".into(), i64_ty()),
                ("__v0_0".into(), i64_ty()),
                ("__v1_0".into(), arc()),
                ("__v2_0".into(), arc()),
                ("__v2_1".into(), arc()),
            ],
            variants: vec![
                VariantDef {
                    name: "Leaf".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), i64_ty())],
                },
                VariantDef {
                    name: "One".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), arc())],
                },
                VariantDef {
                    name: "Two".into(),
                    discriminant: 2,
                    fields: vec![("0".into(), arc()), ("1".into(), arc())],
                },
            ],
            disc_index_safe: true,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: None,
        };

        // The shipped declining statement, `_6 = &((*_1) as Two).0`, on a
        // markers-everywhere body: the ROOT parameter is a bare marker too.
        let two_field_0 = Place {
            local: 1,
            projections: vec![Projection::Deref, Projection::Downcast(2), Projection::Field(0)],
        };
        let markers_everywhere =
            || body(vec![Ty::Unit, Ty::Ref { mutable: false, inner: Box::new(marker("Tree")) }]);
        let with_table = |defs: DatatypeDefs| {
            let mut b = markers_everywhere();
            b.datatype_defs = defs;
            b
        };

        // 1. WITH the entry, the downcast types — the R0 decline is repaired, and
        //    to exactly the type the inline definition produced (see the sibling
        //    test's `with_root_definition` assertion, also `Some(arc())`). BOTH
        //    definitional shapes must do it: the ADT one is what the producer
        //    actually files for `Tree`, and it is the shape the narrow carrier
        //    could not hold at all.
        for (label, def) in [("Ty::Datatype", &tree_datatype_def), ("Ty::Adt", &tree_adt_def)] {
            let defs = DatatypeDefs::from([("Tree".to_string(), def.clone())]);
            assert_eq!(
                place_type(&with_table(defs.clone()), &two_field_0),
                Some(arc()),
                "{label}: a bare root marker plus its explicit table entry must type \
                 `_6 = &((*_1) as Two).0`",
            );
            assert_eq!(
                modeled_enum_variant_count(&defs, &marker("Tree")),
                Some(3),
                "{label}: the variant count comes back through the table",
            );
        }
        // The ADT entry additionally carries what the narrow value type had
        // nowhere to put: the per-variant DISCRIMINANTS a `SwitchInt` compares
        // against. Losing them would be a WRONG fact, not a lossy one.
        let Some(Ty::Adt { variants, .. }) = trust_types::resolve_datatype_marker(
            &DatatypeDefs::from([("Tree".to_string(), tree_adt_def.clone())]),
            &marker("Tree"),
        ) else {
            panic!("the ADT definition resolves as an ADT");
        };
        assert_eq!(variants.iter().map(|v| v.discriminant).collect::<Vec<_>>(), vec![0, 1, 2]);

        // 2. WITHOUT an entry, everything declines exactly as before the table
        //    existed. (A STRUCTURELESS entry is not an entry: honouring it would
        //    resolve the marker to itself and hand back a zero-variant enum. Nor
        //    is an entry that names something OTHER than its key.)
        for defs in [
            DatatypeDefs::new(),
            DatatypeDefs::from([(
                "Tree".to_string(),
                Ty::Datatype {
                    name: "Tree".into(),
                    variants: trust_types::DatatypeVariants::new(),
                },
            )]),
            DatatypeDefs::from([(
                "Tree".to_string(),
                Ty::Datatype { name: "NotTree".into(), variants: tree_variants.clone() },
            )]),
        ] {
            assert_eq!(
                place_type(&with_table(defs.clone()), &two_field_0),
                None,
                "an unlisted (or vacuously listed) marker must decline exactly as today",
            );
            assert_eq!(modeled_enum_variant_count(&defs, &marker("Tree")), None);
        }

        // 3. An entry for a DIFFERENT name does not bind. Resolution is a lookup
        //    keyed by the marker's OWN name; a table that happens to define some
        //    other datatype tells us nothing about this one.
        let other_name = DatatypeDefs::from([(
            "NotTree".to_string(),
            Ty::Datatype { name: "NotTree".into(), variants: tree_variants.clone() },
        )]);
        assert_eq!(
            place_type(&with_table(other_name.clone()), &two_field_0),
            None,
            "a definition filed under another name must not bind this marker",
        );
        assert_eq!(modeled_enum_variant_count(&other_name, &marker("Tree")), None);

        // 4. The withdrawn fail-open design, as a failing assertion. Two
        //    instantiations of one generic cut point are DIFFERENT types; they
        //    stay unequal, and — the part a body-wide by-name search got wrong —
        //    an entry for one must not answer for the other.
        let u8_name = "krate::Foo<std::vec::Vec<u8>>";
        let i32_name = "krate::Foo<std::vec::Vec<i32>>";
        assert!(!ty_eq(&marker(u8_name), &marker(i32_name)));
        let u8_only = DatatypeDefs::from([(
            u8_name.to_string(),
            Ty::Datatype {
                name: u8_name.into(),
                variants: vec![("Mk".to_string(), vec![("0".to_string(), i64_ty())])],
            },
        )]);
        assert_eq!(
            modeled_enum_variant_count(&u8_only, &marker(u8_name)),
            Some(1),
            "the listed instantiation resolves",
        );
        assert_eq!(
            modeled_enum_variant_count(&u8_only, &marker(i32_name)),
            None,
            "`Foo<Vec<i32>>` must NOT pick up `Foo<Vec<u8>>`'s definition — this is the \
             fail-open that sank the by-name body-search repair",
        );
        // The same, one layer down, where the withdrawn design actually failed:
        // `compact_oversized_field`'s generics-ERASED fallback name must not
        // acquire either instantiation's structure.
        assert_eq!(
            modeled_enum_variant_count(&u8_only, &marker("krate::Foo")),
            None,
            "a generics-erased marker must not bind an instantiated definition",
        );
    }

    /// The rewrite `trust_mir_extract::ty_convert` now performs: every occurrence
    /// of the canonical cut point `name` becomes its bare by-name marker.
    ///
    /// This is a MODEL of the producer, written here because no `cargo test` in
    /// this repo can run the producer (the fold corpora are checked-in JSON from
    /// a prebuilt `trustc`; exercising a `ty_convert` change needs a full
    /// bootstrap). It is a faithful model for `Tree` specifically, and the test
    /// below proves that rather than assuming it: `Def1(Tree)` computed this way
    /// is BYTE-IDENTICAL to the definition the shipped dump already carries at
    /// its walk root, so the table entry is transcribed from the producer's own
    /// output and not invented here.
    fn flip_cut_point(ty: &Ty, name: &str) -> Ty {
        let go = |t: &Ty| flip_cut_point(t, name);
        match ty {
            Ty::Adt { name: n, .. } if n == name => {
                Ty::Datatype { name: name.to_string(), variants: vec![] }
            }
            Ty::Adt {
                name: n,
                fields,
                variants,
                disc_index_safe,
                faithful_enum_repr,
                layout,
                enum_layout,
                adt_kind,
            } => Ty::Adt {
                name: n.clone(),
                fields: fields.iter().map(|(f, t)| (f.clone(), go(t))).collect(),
                variants: variants
                    .iter()
                    .map(|v| VariantDef {
                        name: v.name.clone(),
                        discriminant: v.discriminant,
                        fields: v.fields.iter().map(|(f, t)| (f.clone(), go(t))).collect(),
                    })
                    .collect(),
                disc_index_safe: *disc_index_safe,
                faithful_enum_repr: *faithful_enum_repr,
                layout: layout.clone(),
                enum_layout: enum_layout.clone(),
                adt_kind: *adt_kind,
            },
            Ty::Datatype { name: n, variants } => Ty::Datatype {
                name: n.clone(),
                variants: variants
                    .iter()
                    .map(|(c, fs)| {
                        (c.clone(), fs.iter().map(|(f, t)| (f.clone(), go(t))).collect())
                    })
                    .collect(),
            },
            Ty::Ref { mutable, inner } => Ty::Ref { mutable: *mutable, inner: Box::new(go(inner)) },
            Ty::RawPtr { mutable, pointee } => {
                Ty::RawPtr { mutable: *mutable, pointee: Box::new(go(pointee)) }
            }
            Ty::Slice { elem } => Ty::Slice { elem: Box::new(go(elem)) },
            Ty::Array { elem, len } => Ty::Array { elem: Box::new(go(elem)), len: *len },
            Ty::SymArray { elem, len_sym } => {
                Ty::SymArray { elem: Box::new(go(elem)), len_sym: len_sym.clone() }
            }
            Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(go).collect()),
            other => other.clone(),
        }
    }

    /// R0 is gone in the bytes a real `trustc` wrote — one rustc type, one `Ty`.
    ///
    /// R0 was: a canonical cut point is emitted as its FULL DEFINITION at the
    /// outermost nominal position of a `convert_ty` walk and as a bare marker
    /// everywhere else, so ONE rustc type reaches the dump as SEVERAL `ty_eq`-
    /// unequal `Ty` values and `all_assignments_match` declines a well-typed body.
    ///
    /// This test used to prove that by REWRITING the shipped fixture in-process
    /// (the producer had not shipped yet, so the "after" state did not exist on
    /// disk). That is deleted: a test that flips the body itself passes just as
    /// well against a producer that never emits a marker, which is exactly what
    /// happened between 2026-07-13 and 2026-08-04 — `nominal_frontier` had no
    /// `TyKind::Pat` arm, `NonNull`'s only field IS a pattern type, so the cut set
    /// was empty on every real body and this test was green over bytes that
    /// carried `SOURCE::Tree` as 7 structured `Ty::Adt`s and 24 bare markers.
    ///
    /// It now reads the shipped bytes and asserts the END STATE directly. The
    /// witness is `fixtures/structural-fold-corpus/xor_all.json`, whose cycle
    /// `Tree -> Arc -> NonNull -> ArcInner -> Tree` is cut at `Tree` (the
    /// shallowest def path in the cycle — `canonical_cut_key`'s first component).
    /// The statement that used to pay for R0 is `_6 = &((*_1) as Two).0`: the
    /// rvalue typed to one spelling while local 6 was declared with the other, so
    /// `assignment_types_match` declined a perfectly well-typed body. It now
    /// matches, and it matches THROUGH THE TABLE — the last assertion strips the
    /// table and requires the decline to come back, so nothing here is resolving
    /// a marker by name against whatever definitions are in scope.
    #[test]
    fn r0_is_gone_on_the_shipped_bytes_one_rustc_type_now_yields_one_ty() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures/structural-fold-corpus/xor_all.json");
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let shipped: VerifiableFunction = serde_json::from_slice(&bytes)
            .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));

        // `_6 = &((*_1) as Two).0` — located by shape, not by index, so a fixture
        // regeneration that renumbers blocks cannot silently make this vacuous.
        let two_field_0 = Place {
            local: 1,
            projections: vec![Projection::Deref, Projection::Downcast(2), Projection::Field(0)],
        };
        let (dest, rvalue) =
            shipped
                .body
                .blocks
                .iter()
                .flat_map(|b| &b.stmts)
                .find_map(|s| match s {
                    Statement::Assign {
                        place, rvalue: rv @ Rvalue::Ref { place: p, .. }, ..
                    } if *p == two_field_0 => Some((place.clone(), rv.clone())),
                    _ => None,
                })
                .expect("the shipped fixture carries `_6 = &((*_1) as Two).0`");
        assert_eq!(dest.local, 6, "the shipped destination is local 6");

        // ── The cut point is a MARKER at the walk root, not a definition ─────
        // This is the half that could not be asserted before the producer fix,
        // and it is the whole of R0: the root is spelled exactly as every nested
        // occurrence is.
        let Ty::Ref { inner: shipped_tree, .. } = &shipped.body.locals[1].ty else {
            panic!("local 1 is `&Tree`");
        };
        let Ty::Datatype { name: cut_name, variants } = shipped_tree.as_ref() else {
            panic!(
                "R0: the SHIPPED root spelling of `Tree` must be a bare `Ty::Datatype` \
                 marker — a full `Ty::Adt` here means the producer regressed to the \
                 root-relative lowering",
            );
        };
        assert!(variants.is_empty(), "a cut-point marker carries NO structure");
        // EXACT, not a suffix test: the identity policy is "the crate-qualified
        // definition-site path" (`with_resolve_crate_name!` in
        // `safe_def_path_str`, `bd2d6ed1fc`), and that is one string, not a
        // family.
        assert_eq!(cut_name, "SOURCE::Tree");

        // ── …and its structure lives ONCE, out of band ──────────────────────
        let definition = trust_types::datatype_definition(&shipped.body.datatype_defs, cut_name)
            .expect("the producer filed `SOURCE::Tree`'s definition in the table");
        let Ty::Adt { name: def_name, variants: def_variants, .. } = definition else {
            panic!("the recorded definition is a full `Ty::Adt`");
        };
        assert_eq!(def_name, cut_name, "a definition is filed under the name it claims");
        assert_eq!(def_variants.len(), 3, "`Tree` is the 3-constructor tree enum");

        // ── ONE rustc type, ONE `Ty` value ──────────────────────────────────
        // `Arc<Tree>` as `Tree`'s own field and `Arc<Tree>` as local 6's pointee
        // are the two positions that disagreed under R0. They are now equal, and
        // the assignment that used to decline now types.
        let field_arc =
            place_type(&shipped.body, &two_field_0).expect("the downcast types through the table");
        let Ty::Ref { inner: local6_arc, .. } = &shipped.body.locals[6].ty else {
            panic!("local 6 is `&Arc<Tree>`");
        };
        assert!(
            ty_eq(&field_arc, local6_arc),
            "one rustc type, one `Ty`: `Arc<Tree>` as `Tree`'s field and as local 6's \
             pointee must be EQUAL",
        );
        assert!(
            assignment_types_match(&shipped.body, &dest, &rvalue),
            "`_6 = &((*_1) as Two).0` types on the shipped bytes",
        );

        // ── …and the repair is the TABLE, never a by-name search ────────────
        // Withdrawn design: searching the body for a same-name definition is
        // fail-OPEN, because `compact_oversized_field` emits the IDENTICAL bare
        // shape for a SIZE BOUND rather than a back-edge.
        let mut no_table = shipped.clone();
        no_table.body.datatype_defs = DatatypeDefs::new();
        assert!(
            place_type(&no_table.body, &two_field_0).is_none()
                || !assignment_types_match(&no_table.body, &dest, &rvalue),
            "with the table stripped the downcast must stop typing — a consumer may \
             never resolve a marker by name",
        );
    }

    /// NO OVER-MERGE, with the widened carrier in play.
    ///
    /// An over-merging canonicalization is strictly worse than R0's fail-closed
    /// decline, so the three pairs that could plausibly collapse are pinned to
    /// stay UNEQUAL — and, now that entries are whole `Ty` values, to stay
    /// mutually unresolvable through the table as well. A marker-inequality
    /// assertion alone would not catch a table that answers for both.
    #[test]
    fn the_widened_table_never_merges_two_distinct_types() {
        let marker = |name: &str| Ty::Datatype { name: name.into(), variants: vec![] };
        let def = |name: &str, field: Ty| Ty::Datatype {
            name: name.into(),
            variants: vec![("Mk".to_string(), vec![("0".to_string(), field)])],
        };
        let u8_ty = || Ty::Int { width: 8, signed: false };
        let i32_ty = || Ty::Int { width: 32, signed: true };

        // PAIR 1 — two instantiations of one generic cut point. `canonical_cut_ref`
        // renders the INSTANTIATED path, so they are two keys with two entries.
        let foo_u8 = "krate::Foo<std::vec::Vec<u8>>";
        let foo_i32 = "krate::Foo<std::vec::Vec<i32>>";
        // PAIR 2 — two distinct cycles whose types share a leaf name. The def path
        // is rendered untrimmed, so the module prefix survives.
        let alpha = "krate::alpha::Node";
        let beta = "krate::beta::Node";
        // PAIR 3 — a REAL cut point and a `compact_oversized_field` marker of the
        // same generics-erased name. Only the cut point is ever written to the
        // table (`record_cut_definition` is the sole writer), so the compacted one
        // resolves to nothing. This is the withdrawn by-name search's fail-open.
        let cut = "krate::Big<u8>";
        let compacted = "krate::Big";

        let mut defs = DatatypeDefs::new();
        for (name, field) in [
            (foo_u8, u8_ty()),
            (foo_i32, i32_ty()),
            (alpha, u8_ty()),
            (beta, i32_ty()),
            (cut, u8_ty()),
        ] {
            assert!(trust_types::insert_datatype_def(&mut defs, def(name, field)));
        }

        for (a, b) in [(foo_u8, foo_i32), (alpha, beta), (cut, compacted)] {
            assert!(!ty_eq(&marker(a), &marker(b)), "`{a}` and `{b}` must stay UNEQUAL");
            let ra = trust_types::resolve_datatype_marker(&defs, &marker(a));
            let rb = trust_types::resolve_datatype_marker(&defs, &marker(b));
            assert_ne!(ra, rb, "`{a}` and `{b}` must not resolve to the same definition");
        }

        // The compacted marker resolves to NOTHING at all — it is a SIZE BOUND,
        // never a cut point, and nothing may bind it.
        assert_eq!(trust_types::resolve_datatype_marker(&defs, &marker(compacted)), None);
        assert_eq!(
            trust_types::resolve_datatype_marker(&defs, &marker("__trust_compacted_aggregate")),
            None,
        );
        // Each real entry answers for its OWN key and no other.
        assert_eq!(modeled_enum_variant_count(&defs, &marker(foo_u8)), Some(1));
        assert_eq!(
            trust_types::resolve_datatype_marker(&defs, &marker(foo_u8)),
            Some(def(foo_u8, u8_ty())),
        );
        assert_eq!(
            trust_types::resolve_datatype_marker(&defs, &marker(alpha)),
            Some(def(alpha, u8_ty())),
        );
    }

    // --- trait-object raw-pointer casts (vtable slice 19) ---------------------
    //
    // Every case below holds `trait_name` CONSTANT and varies only `principal_key`, so
    // each assertion is about the faithful identity alone. Under the old erased keying
    // all of them compared equal, which is the defect.

    fn dyn_pointee(principal_key: &str) -> Ty {
        Ty::Dynamic { trait_name: "krate::Trait".into(), principal_key: Some(principal_key.into()) }
    }

    fn unkeyed_dyn_pointee() -> Ty {
        Ty::Dynamic { trait_name: "krate::Trait".into(), principal_key: None }
    }

    /// The `remove_auto` case from `tests/ui/cast/ptr-to-trait-obj-ok.rs`, a `//@ check-pass`
    /// file: `*mut (dyn Trait + Send) as *mut dyn Trait`. The keys DIFFER (auto traits are
    /// in the key) but the cast is LEGAL RUST that reaches MIR, so a blanket key comparison
    /// would be a pure coverage loss on valid code — a drop-in-compatibility defect.
    #[test]
    fn raw_ptr_dyn_cast_accepts_auto_trait_removal() {
        let source = dyn_pointee("krate::Trait+core::marker::Send");
        let destination = dyn_pointee("krate::Trait");
        assert_ne!(source, destination, "precondition: the two keys really do differ");
        assert!(raw_pointer_cast_supported(&source, &destination));
        // Dropping ONE of several autos is equally legal.
        assert!(raw_pointer_cast_supported(
            &dyn_pointee("krate::Trait+core::marker::Send+core::marker::Sync"),
            &dyn_pointee("krate::Trait+core::marker::Send"),
        ));
        // The identity cast is of course still accepted.
        assert!(raw_pointer_cast_supported(
            &dyn_pointee("krate::Trait+core::marker::Send"),
            &dyn_pointee("krate::Trait+core::marker::Send"),
        ));
    }

    /// The converse direction is NOT a legal upcast — rustc rejects adding an auto trait
    /// in `rustc_hir_typeck/src/cast.rs` — so the subset check must be directional.
    #[test]
    fn raw_ptr_dyn_cast_rejects_auto_trait_addition() {
        assert!(!raw_pointer_cast_supported(
            &dyn_pointee("krate::Trait"),
            &dyn_pointee("krate::Trait+core::marker::Send"),
        ));
        assert!(!raw_pointer_cast_supported(
            &dyn_pointee("krate::Trait+core::marker::Send"),
            &dyn_pointee("krate::Trait+core::marker::Sync"),
        ));
    }

    /// Principal arguments and associated-type bindings get EXACT equality, not subset:
    /// `dyn Convert<u32>` and `dyn Convert<u64>` are different types with different
    /// vtables. (Upstream HIR typeck already rejects these before MIR; this is the
    /// fail-closed backstop, not the primary gate.)
    #[test]
    fn raw_ptr_dyn_cast_rejects_differing_args_and_bindings() {
        assert!(!raw_pointer_cast_supported(
            &dyn_pointee("krate::Convert<u32>"),
            &dyn_pointee("krate::Convert<u64>"),
        ));
        assert!(!raw_pointer_cast_supported(
            &dyn_pointee("core::iter::Iterator+[core::iter::Iterator::Item=u32]"),
            &dyn_pointee("core::iter::Iterator+[core::iter::Iterator::Item=u64]"),
        ));
        // A binding may not be dropped the way an auto trait may.
        assert!(!raw_pointer_cast_supported(
            &dyn_pointee("core::iter::Iterator+[core::iter::Iterator::Item=u32]"),
            &dyn_pointee("core::iter::Iterator"),
        ));
    }

    /// An unrenderable identity cannot be shown equal to anything, including itself:
    /// falling back to the erased `trait_name` is exactly the defect being closed.
    #[test]
    fn raw_ptr_dyn_cast_without_principal_key_fails_closed() {
        assert!(!raw_pointer_cast_supported(&unkeyed_dyn_pointee(), &unkeyed_dyn_pointee()));
        assert!(!raw_pointer_cast_supported(&unkeyed_dyn_pointee(), &dyn_pointee("krate::Trait")));
        assert!(!raw_pointer_cast_supported(&dyn_pointee("krate::Trait"), &unkeyed_dyn_pointee()));
    }

    /// The parser admits the renderer's grammar and refuses everything else, including the
    /// historical hand-written `"A + B + Send"` spelling (spaces around the separator) that
    /// `faithful_principal_key` never emits.
    #[test]
    fn principal_key_parser_admits_the_grammar_and_refuses_the_rest() {
        let parsed = parse_principal_key(
            "krate::Convert<u32>+[core::iter::Iterator::Item=u64]+core::marker::Send",
        )
        .expect("the renderer's grammar parses");
        assert_eq!(parsed.principal, "krate::Convert<u32>");
        assert_eq!(parsed.bindings, vec!["core::iter::Iterator::Item=u64"]);
        assert_eq!(parsed.autos, vec!["core::marker::Send"]);

        // A `+` nested inside brackets is part of a component, never a separator.
        let nested = parse_principal_key("krate::F<krate::G<a+b>>").expect("balanced");
        assert_eq!(nested.principal, "krate::F<krate::G<a+b>>");
        assert!(nested.autos.is_empty());

        assert!(parse_principal_key("").is_none(), "empty key");
        assert!(parse_principal_key("+core::marker::Send").is_none(), "empty principal");
        assert!(parse_principal_key("krate::Trait<u32").is_none(), "unbalanced");
        assert!(parse_principal_key("krate::Trait>").is_none(), "unbalanced");
        assert!(parse_principal_key("krate::Trait+").is_none(), "empty trailing segment");
        assert!(parse_principal_key("krate::Trait+[]").is_none(), "empty binding");
        assert!(
            parse_principal_key("core::fmt::Debug + core::clone::Clone + Send").is_none(),
            "the legacy spaced multi-bound spelling is outside the grammar and fails closed",
        );
    }
}
