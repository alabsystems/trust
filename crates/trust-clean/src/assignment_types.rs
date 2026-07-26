//! Projection-aware assignment typing for TrustClean recognizers.
//!
//! Trust MIR is a public, deserializable schema. Rustc emits well-typed assignments,
//! but a diagnostic or certificate entry point can also receive a hand-built body.
//! Recognizers which chase an `Assign` must therefore establish the destination and
//! rvalue types themselves; shape recognition and safety VCs are not a type checker.

use trust_types::{
    AggregateKind, BinOp, CallableKind, ConstValue, Operand, Place, Projection, Rvalue, Statement,
    Ty, UnOp, VerifiableBody,
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
pub(crate) fn modeled_enum_variant_count(ty: &Ty) -> Option<usize> {
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

fn field_ty(ty: &Ty, variant: Option<usize>, field: usize) -> Option<Ty> {
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
                let count = match &ty {
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
                ty = field_ty(&ty, downcast.take(), *field)?;
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
    let expected = [("Less", -1_i128), ("Equal", 0), ("Greater", 1)];
    variants.len() == expected.len()
        && variants.iter().zip(expected).all(|(variant, (name, discriminant))| {
            variant.name == name
                && (variant.discriminant == discriminant
                    || (name == "Less" && variant.discriminant == 255))
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

fn raw_pointer_cast_supported(source: &Ty, destination: &Ty) -> bool {
    match destination {
        // Length-metadata pointers may retain compatible length metadata or be
        // produced by the one reconstructable thin-to-fat unsize coercion.
        Ty::Slice { .. } | Ty::Str => {
            matches!(source, Ty::Slice { .. } | Ty::Str)
                || pointer_pointee_coercion(source, destination)
        }
        // Vtable metadata is identity-bearing; the schema cannot prove trait
        // upcasting or a concrete implementation, so only the exact trait stays.
        Ty::Dynamic { trait_name: destination_trait } => {
            matches!(source, Ty::Dynamic { trait_name: source_trait }
                if source_trait == destination_trait)
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
        (Ty::RawPtr { .. }, Ty::Adt { name, .. })
            if name == "core::ptr::non_null::NonNull" =>
        {
            true
        }
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
                && place_type(body, place).is_some_and(|ty| match ty {
                    Ty::Adt { fields, variants, faithful_enum_repr, .. } => {
                        !variants.is_empty()
                            || (faithful_enum_repr.is_none()
                                && legacy_discriminant_tag_matches(&fields, expected))
                    }
                    Ty::Datatype { variants, .. } => !variants.is_empty(),
                    _ => false,
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
        }
    }

    #[test]
    fn unit_constant_requires_the_exact_canonical_marker_type() {
        let empty_adt = |name: &str| Ty::adt(name, vec![]);
        assert!(constant_matches_type(
            &ConstValue::Unit,
            &empty_adt("core::marker::PhantomData")
        ));
        for forged in [
            "T",
            "user::Marker",
            "user::Never",
            "user::core::marker::PhantomData",
        ] {
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
        let legacy = Ty::Adt { adt_kind: None, layout: None, 
            name: "demo::Legacy".into(),
            fields: vec![("__v0_0".into(), i32_ty.clone())],
            variants: vec![variant.clone()],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let first_class = Ty::Adt { adt_kind: None, layout: None,
            name: "demo::FirstClass".into(),
            fields: vec![("0".into(), i32_ty.clone())],
            variants: vec![variant],
            disc_index_safe: true,
            faithful_enum_repr: Some(None), enum_layout: None, };
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
        let legacy_option = Ty::Adt { adt_kind: None, layout: None, 
            name: "demo::OptionBool".into(),
            fields: vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                ("__v1_0".into(), Ty::Bool),
            ],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let body = body(vec![legacy_option]);
        assert!(assignment_types_match(
            &body,
            &Place::local(0),
            &Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "demo::OptionBool".into(),
                    variant: 0,
                    active_field: None,
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
                },
                vec![],
            ),
        ));
    }

    #[test]
    fn legacy_flattened_downcast_requires_one_canonical_payload_layout() {
        let tag = || ("__tag".into(), Ty::Int { width: 64, signed: true });
        let legacy = |fields| Ty::Adt { adt_kind: None, layout: None, 
            name: "demo::OptionPair".into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
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
        let legacy = |name: &str, fields| Ty::Adt { adt_kind: None, layout: None, 
            name: name.into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
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
                AggregateKind::Adt { name: name.into(), variant, active_field },
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
        let legacy = |fields| Ty::Adt { adt_kind: None, layout: None, 
            name: "demo::LegacyEither".into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
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
        let ordering = |name: &str, fields| Ty::Adt { adt_kind: None, layout: None, 
            name: name.into(),
            fields,
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
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
        let fake_ordering = Ty::Adt { adt_kind: None, layout: None, 
            name: "user::Ordering".into(),
            fields: vec![("__tag".into(), Ty::Int { width: 64, signed: true })],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
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
}
