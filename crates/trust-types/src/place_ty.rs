//! Pure projection typing over the shared verification model.
//! Consumers retain their own fact, budget and caching policy.

use crate::{Projection, Ty};

pub fn project_ty_cow<'a>(ty: &'a Ty, proj: &Projection) -> Option<std::borrow::Cow<'a, Ty>> {
    use std::borrow::Cow;
    match proj {
        Projection::Downcast(_) => Some(Cow::Borrowed(ty)),
        // These carry an inline replacement `Ty` in the projection itself; it is not a
        // subtree of `ty`, so it must be owned (matching `project_ty`'s `ty.clone()`).
        Projection::OpaqueCast(t) | Projection::UnwrapUnsafeBinder(t) => {
            Some(Cow::Owned(t.clone()))
        }
        Projection::Field(idx) => match ty {
            Ty::Tuple(fields) => fields.get(*idx).map(Cow::Borrowed),
            Ty::Adt { fields, .. } => fields.get(*idx).map(|(_, field_ty)| Cow::Borrowed(field_ty)),
            Ty::Closure { upvars, .. } => upvars.get(*idx).map(Cow::Borrowed),
            Ty::Datatype { variants, .. } if variants.len() == 1 => {
                variants[0].1.get(*idx).map(|(_, field_ty)| Cow::Borrowed(field_ty))
            }
            _ => None,
        },
        Projection::Deref => match ty {
            Ty::Ref { inner, .. } => Some(Cow::Borrowed(inner)),
            Ty::RawPtr { pointee, .. } => Some(Cow::Borrowed(pointee)),
            _ => None,
        },
        Projection::Index(_) | Projection::ConstantIndex { .. } => match ty {
            // Trust: piece #7a — indexing a const-generic array steps to its
            // element type, exactly like a concrete `[T; N]`.
            Ty::Array { elem, .. } | Ty::Slice { elem } | Ty::SymArray { elem, .. } => {
                Some(Cow::Borrowed(elem))
            }
            _ => None,
        },
        // Subslice SYNTHESIZES a new `Array`/`Slice` (new length / re-borrowed elem) —
        // the one arm that must allocate. The element subtree is still borrowed-then-
        // cloned exactly once, never the parent.
        Projection::Subslice { from, to, from_end } => match ty {
            Ty::Array { elem, len } => {
                let result_len = if *from_end {
                    len.checked_sub(*from as u64)?.checked_sub(*to as u64)?
                } else {
                    if to < from || *to as u64 > *len {
                        return None;
                    }
                    (to - from) as u64
                };
                Some(Cow::Owned(Ty::Array { elem: elem.clone(), len: result_len }))
            }
            Ty::Slice { elem } => Some(Cow::Owned(Ty::Slice { elem: elem.clone() })),
            _ => None,
        },
    }
}

pub fn place_ty_step_input<'a>(
    defs: &'a crate::DatatypeDefs,
    ty: std::borrow::Cow<'a, Ty>,
) -> (std::borrow::Cow<'a, Ty>, bool) {
    match crate::datatype_marker_definition(defs, ty.as_ref()) {
        Some(definition) => (std::borrow::Cow::Borrowed(definition), true),
        None => (ty, false),
    }
}

pub fn step_place_ty_cow<'a>(
    ty: std::borrow::Cow<'a, Ty>,
    proj: &Projection,
) -> Option<std::borrow::Cow<'a, Ty>> {
    use std::borrow::Cow;
    match ty {
        // Still borrowing the function's declared type — project by reference; only the
        // synthetic arms allocate (see `project_ty_cow`), and the borrow keeps lifetime
        // `'a` (the function's), so subsequent borrowed steps stay clone-free.
        Cow::Borrowed(t) => project_ty_cow(t, proj),
        // Already owning a synthetic intermediate — its borrow cannot escape this frame,
        // so resolve against it and clone the (small) result to re-own.
        Cow::Owned(t) => project_ty_cow(&t, proj).map(|c| Cow::Owned(c.into_owned())),
    }
}

fn select_adt_variant_field(fields: &[(String, Ty)], v: usize, idx: usize) -> Option<&Ty> {
    fields
        .iter()
        .filter(|(name, _)| {
            name.strip_prefix("__v").and_then(|rest| rest.split_once('_')).is_some_and(
                |(digits, _)| {
                    !digits.is_empty()
                        && digits.bytes().all(|byte| byte.is_ascii_digit())
                        && (digits.len() == 1 || !digits.starts_with('0'))
                        && digits.parse::<usize>().ok() == Some(v)
                },
            )
        })
        .nth(idx)
        .map(|(_, t)| t)
}

pub fn place_ty_step<'a>(
    defs: &'a crate::DatatypeDefs,
    mut ty: std::borrow::Cow<'a, Ty>,
    proj: &Projection,
    pending_variant: &mut Option<usize>,
) -> Option<std::borrow::Cow<'a, Ty>> {
    use std::borrow::Cow;
    // R0: widen a bare `Ty::Datatype { variants: [] }` marker through THIS
    // body's explicit out-of-band table before the step reads it. Applied at
    // every step, not just the base, because a datatype reached partway down
    // a chain (a recursive child) is spelled bare too. Resolution is shallow
    // — one level per step — so it terminates on a self-recursive type, and
    // it is the identity on every other shape and on a marker the table does
    // not define, so a place that already typed keeps its exact result.
    // (`place_ty_step_input` is the same resolution, for a walker that must
    // judge the resolved type BEFORE stepping; on its output this is the
    // identity, since a definition is never a bare marker.)
    if let Some(resolved) = crate::datatype_marker_definition(defs, &ty) {
        ty = Cow::Borrowed(resolved);
    }
    match proj {
        Projection::Downcast(v) => {
            // A downcast does not change the modeled type; it only records
            // which variant a following `Field` projection is relative to.
            *pending_variant = Some(*v);
        }
        Projection::Field(idx) => {
            if let (Some(v), Ty::Adt { .. }) = (*pending_variant, ty.as_ref()) {
                *pending_variant = None;
                ty = match ty {
                    Cow::Borrowed(Ty::Adt { fields, .. }) => {
                        Cow::Borrowed(select_adt_variant_field(fields, v, *idx)?)
                    }
                    Cow::Owned(Ty::Adt { fields, .. }) => {
                        Cow::Owned(select_adt_variant_field(&fields, v, *idx)?.clone())
                    }
                    _ => return None,
                };
            } else if matches!(ty.as_ref(), Ty::Datatype { .. }) {
                // Lever A: variant-relative datatype field. `Field` after a
                // `Downcast(v)` selects variant v's i-th field; a bare `Field`
                // on a single-variant datatype selects variant 0's; multi-variant
                // without a downcast is ambiguous → fail closed.
                let v = match pending_variant.take() {
                    Some(v) => v,
                    None
                        if matches!(
                            ty.as_ref(),
                            Ty::Datatype { variants, .. } if variants.len() == 1
                        ) =>
                    {
                        0
                    }
                    None => return None,
                };
                ty = match ty {
                    Cow::Borrowed(Ty::Datatype { variants, .. }) => Cow::Borrowed(
                        variants.get(v).and_then(|(_, fs)| fs.get(*idx)).map(|(_, t)| t)?,
                    ),
                    Cow::Owned(Ty::Datatype { variants, .. }) => Cow::Owned(
                        variants.get(v).and_then(|(_, fs)| fs.get(*idx)).map(|(_, t)| t.clone())?,
                    ),
                    _ => return None,
                };
            } else {
                *pending_variant = None;
                ty = step_place_ty_cow(ty, proj)?;
            }
        }
        _ => {
            *pending_variant = None;
            ty = step_place_ty_cow(ty, proj)?;
        }
    }
    Some(ty)
}

#[cfg(test)]
mod variant_spelling_tests {
    use std::borrow::Cow;

    use super::*;

    fn selected_field(fields: &[(&str, Ty)], variant: usize, index: usize) -> Option<Ty> {
        let ty = Ty::Adt {
            name: "OriginalVariantCarrier".into(),
            fields: fields.iter().map(|(name, ty)| ((*name).into(), ty.clone())).collect(),
            variants: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        };
        let defs = crate::DatatypeDefs::new();
        let mut pending = None;
        let downcast =
            place_ty_step(&defs, Cow::Borrowed(&ty), &Projection::Downcast(variant), &mut pending)?;
        place_ty_step(&defs, downcast, &Projection::Field(index), &mut pending).map(Cow::into_owned)
    }

    #[test]
    fn canonical_downcast_variant_spelling_preserves_fields() {
        for (name, variant) in
            [("__v0_", 0), ("__v0_1", 0), ("__v12_1", 12), ("__v123456_field", 123456)]
        {
            assert_eq!(selected_field(&[(name, Ty::Bool)], variant, 0), Some(Ty::Bool), "{name}");
        }
    }

    #[test]
    fn noncanonical_downcast_variant_spelling_is_not_an_alias() {
        for (name, variant) in [
            ("__v+0_0", 0),
            ("__v00_0", 0),
            ("__v+12_0", 12),
            ("__v012_0", 12),
            ("__v_0", 0),
            ("__v-0_0", 0),
            ("__v 0_0", 0),
            ("__v０_0", 0),
            ("__v١٢_0", 12),
            ("__v184467440737095516160_0", 0),
        ] {
            assert!(
                selected_field(&[(name, Ty::Bool)], variant, 0).is_none(),
                "{name} must not alias variant {variant}"
            );
        }
    }

    #[test]
    fn aliased_variant_cannot_shift_selected_field() {
        let actual = Ty::Int { width: 8, signed: false };
        for alias in ["__v+0_0", "__v00_0"] {
            let fields = [(alias, Ty::Bool), ("__v0_0", actual.clone())];
            assert_eq!(selected_field(&fields, 0, 0), Some(actual.clone()));
            assert!(selected_field(&fields, 0, 1).is_none());
        }
    }
}
