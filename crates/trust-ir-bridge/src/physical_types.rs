//! Recover physical cut-point definitions without interpreting SMT datatypes as layouts.
//!
//! The extractor's body-local table can contain either logical `Datatype` models
//! (which may erase pointers) or layout-bearing `Adt` definitions. Only the latter
//! may replace an opaque marker in the native bridge. Normalize the lowering view
//! before type registration AND value lowering so every consumer sees the same
//! fields. The source body, including its authority/digest, stays unchanged.

use std::borrow::Cow;

use trust_types::{AdtKind, DatatypeDefs, TupleLayoutInfo, TupleLayouts, Ty, VerifiableBody};

mod cache;

const MAX_DEPTH: usize = 64;
const MAX_NODES: usize = 16_384;

pub(super) fn body_view(body: &VerifiableBody) -> Cow<'_, VerifiableBody> {
    let mut normalizer = cache::Normalizer::new(&body.datatype_defs);
    if !normalizer.has_physical_definitions() {
        return Cow::Borrowed(body);
    }
    if !crate::physical_body_walk::any_body_type(body, &mut |ty| {
        ty_may_contain_expandable_marker(ty, &body.datatype_defs, 0)
    }) {
        return Cow::Borrowed(body);
    }
    let mut view = body.clone();
    let mut changed = false;
    crate::physical_body_walk::map_body_types(&mut view, &mut |ty| {
        let mapped = normalizer.normalize(ty);
        changed |= mapped != *ty;
        mapped
    });
    if changed { Cow::Owned(view) } else { Cow::Borrowed(body) }
}

/// A function's `tuple_layouts`, re-keyed to the lowering view's type spelling.
///
/// The rows are keyed by the extracted spelling, and `body_view` re-spells every body
/// type through [`normalize`], so a tuple over an expanded cut point would no longer
/// find its row. Re-keying applies the SAME map to each row's key and leaves rustc's
/// numbers alone. It admits no extent: the bridge re-checks every row's field sizes
/// and alignments against its own trust-ir element layouts (`admit_tuple_layout`),
/// and `TupleLayouts::from_rows` drops any key two rows now share with different
/// layouts.
pub(super) fn tuple_layouts_view<'a>(
    layouts: &'a TupleLayouts,
    defs: &DatatypeDefs,
) -> Cow<'a, TupleLayouts> {
    if layouts.is_empty() {
        return Cow::Borrowed(layouts);
    }
    let mut normalizer = cache::Normalizer::new(defs);
    if !normalizer.has_physical_definitions() {
        return Cow::Borrowed(layouts);
    }
    if layouts.target.is_some()
        && layouts.entries.len() == 1
        && layouts.entries[0].is_coherent()
        && !ty_may_contain_expandable_marker(&layouts.entries[0].tuple, defs, 0)
    {
        return Cow::Borrowed(layouts);
    }
    let rows = layouts
        .entries
        .iter()
        .map(|row| TupleLayoutInfo { tuple: normalizer.normalize(&row.tuple), ..row.clone() })
        .collect();
    Cow::Owned(TupleLayouts::from_rows(layouts.target.clone(), rows))
}

pub(super) fn normalize(ty: &Ty, defs: &DatatypeDefs) -> Ty {
    if !has_physical_definitions(defs) {
        return ty.clone();
    }
    normalize_physical(ty, defs)
}

// Both standalone normalization and cache misses enter the identical bounded
// algorithm. Only the immutable-table work filter is hoisted by a cache context.
fn normalize_physical(ty: &Ty, defs: &DatatypeDefs) -> Ty {
    if !ty_may_contain_expandable_marker(ty, defs, 0) {
        return ty.clone();
    }
    let mut budget = MAX_NODES;
    expand(ty, defs, &mut Vec::new(), 0, &mut budget).unwrap_or_else(|| ty.clone())
}

/// Conservative allocation-free pre-filter for [`expand`]: returns `false` only
/// when `expand(ty, defs, ...)` is guaranteed to leave `ty` unchanged because
/// no reachable child in `ty` is a bare datatype marker backed by `Ty::Adt` in
/// `defs`. Returning `true` falls through to [`expand`], which still re-checks
/// full eligibility, cycles, and node/depth budgets.
fn ty_may_contain_expandable_marker(ty: &Ty, defs: &DatatypeDefs, depth: usize) -> bool {
    if depth >= MAX_DEPTH {
        return false;
    }
    if trust_types::bare_datatype_marker_name(ty).is_some() {
        return matches!(trust_types::datatype_marker_definition(defs, ty), Some(Ty::Adt { .. }));
    }
    match ty {
        Ty::Bool
        | Ty::Char
        | Ty::Int { .. }
        | Ty::Float { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Str
        | Ty::Unit
        | Ty::Never => false,
        // Non-bare logical `Datatype` models (non-empty `variants`) are never
        // traversed by `expand`.
        Ty::Datatype { .. } => false,
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
            ty_may_contain_expandable_marker(inner, defs, depth + 1)
        }
        Ty::Array { elem, .. }
        | Ty::Slice { elem }
        | Ty::SymArray { elem, .. }
        | Ty::Seq { elem, .. } => ty_may_contain_expandable_marker(elem, defs, depth + 1),
        Ty::Tuple(fields) => {
            fields.iter().any(|field| ty_may_contain_expandable_marker(field, defs, depth + 1))
        }
        Ty::Adt { fields, variants, .. } => {
            fields.iter().any(|(_, field)| ty_may_contain_expandable_marker(field, defs, depth + 1))
                || variants.iter().any(|variant| {
                    variant.fields.iter().any(|(_, field)| {
                        ty_may_contain_expandable_marker(field, defs, depth + 1)
                    })
                })
        }
        Ty::Closure { upvars, call, .. } => {
            upvars.iter().any(|upvar| ty_may_contain_expandable_marker(upvar, defs, depth + 1))
                || call.as_ref().is_some_and(|sig| {
                    sig.params
                        .iter()
                        .any(|param| ty_may_contain_expandable_marker(param, defs, depth + 1))
                        || sig
                            .ret
                            .as_ref()
                            .is_some_and(|ret| ty_may_contain_expandable_marker(ret, defs, depth + 1))
                })
        }
        Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(|upvar| ty_may_contain_expandable_marker(upvar, defs, depth + 1))
        }
        Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
            sig.params
                .iter()
                .any(|param| ty_may_contain_expandable_marker(param, defs, depth + 1))
                || ty_may_contain_expandable_marker(&sig.ret, defs, depth + 1)
        }
        _ => true,
    }
}

fn has_physical_definitions(defs: &DatatypeDefs) -> bool {
    // Legacy verifier/SMT tables have no physical layouts. Keep them on the
    // borrowed fast path rather than cloning every recursive body to discover
    // that no marker was eligible. This is only a work filter, not admission.
    defs.values().any(|ty| {
        matches!(
            ty,
            Ty::Adt { adt_kind: Some(AdtKind::Struct), layout: Some(_), .. }
                | Ty::Adt {
                    adt_kind: Some(AdtKind::Enum),
                    faithful_enum_repr: Some(_),
                    enum_layout: Some(_),
                    ..
                }
        )
    })
}

fn spend(depth: usize, budget: &mut usize) -> Option<()> {
    if depth >= MAX_DEPTH || *budget == 0 {
        // Distinguish resource exhaustion from an ordinary opaque definition.
        // No partially expanded prefix may survive and unfold further on a
        // second pass through signature/closure registration.
        *budget = 0;
        return None;
    }
    *budget -= 1;
    Some(())
}

/// A bounded, finite spelling: a pointer back-edge retains its nominal pointee.
/// A by-value back-edge never passes `physical_value` in the first place.
fn expand(
    ty: &Ty,
    defs: &DatatypeDefs,
    active: &mut Vec<String>,
    depth: usize,
    budget: &mut usize,
) -> Option<Ty> {
    spend(depth, budget)?;
    if let Some(name) = trust_types::bare_datatype_marker_name(ty) {
        if active.iter().any(|entry| entry == name) {
            return Some(ty.clone());
        }
        let Some(def) = trust_types::datatype_marker_definition(defs, ty) else {
            return Some(ty.clone());
        };
        // In particular, a nonempty logical Datatype is NOT a physical Adt.
        if !matches!(def, Ty::Adt { .. })
            || !physical_value(def, defs, &mut vec![name.to_owned()], 0, budget)
        {
            return (*budget != 0).then(|| ty.clone());
        }
        active.push(name.to_owned());
        let result = expand(def, defs, active, depth + 1, budget);
        active.pop();
        return result;
    }
    let mut out = ty.clone();
    // Include inline definitions too: re-normalizing a registry-refined type
    // must not unfold its recursive pointer back-edge one extra time.
    let pushed_inline = if let Ty::Adt { name, .. } = ty {
        if active.contains(name) {
            false
        } else {
            active.push(name.clone());
            true
        }
    } else {
        false
    };
    let mut child = |ty: &mut Ty| -> Option<()> {
        *ty = expand(ty, defs, active, depth + 1, budget)?;
        Some(())
    };
    match &mut out {
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => child(inner)?,
        Ty::Array { elem, .. }
        | Ty::Slice { elem }
        | Ty::SymArray { elem, .. }
        | Ty::Seq { elem, .. } => child(elem)?,
        Ty::Tuple(fields) => {
            for field in fields {
                child(field)?;
            }
        }
        Ty::Adt { fields, variants, .. } => {
            // `out` is this call's own clone; `make_mut` un-shares each body before the
            // rewrite, so the input `ty` (and every other holder of its bodies) is untouched.
            for (_, field) in fields.make_mut().iter_mut() {
                child(field)?;
            }
            for variant in variants.make_mut().iter_mut() {
                for (_, field) in &mut variant.fields {
                    child(field)?;
                }
            }
        }
        Ty::Closure { upvars, call, .. } => {
            for upvar in upvars {
                child(upvar)?;
            }
            if let Some(sig) = call {
                for param in &mut sig.params {
                    child(param)?;
                }
                if let Some(ret) = &mut sig.ret {
                    child(ret)?;
                }
            }
        }
        Ty::Coroutine { upvars, .. } => {
            for upvar in upvars {
                child(upvar)?;
            }
        }
        Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
            for param in &mut sig.params {
                child(param)?;
            }
            child(&mut sig.ret)?;
        }
        // Logical datatype models remain byte-for-byte logical. In particular,
        // do not turn their pointer-erased nominal children into physical fields.
        Ty::Datatype { .. } => {}
        _ => {}
    }
    if pushed_inline {
        active.pop();
    }
    Some(out)
}

/// `layout: Some` is NOT a Sized witness: rustc can describe a DST's prefix.
/// Establish Sized from the whole by-value shape instead, stopping at pointer
/// edges (a reference value is sized even when its pointee is not).
fn known_sized(
    ty: &Ty,
    defs: &DatatypeDefs,
    active: &mut Vec<String>,
    depth: usize,
    budget: &mut usize,
) -> bool {
    if spend(depth, budget).is_none() {
        return false;
    }
    if let Some(name) = trust_types::bare_datatype_marker_name(ty) {
        if active.iter().any(|entry| entry == name) {
            return false;
        }
        let Some(def) = trust_types::datatype_marker_definition(defs, ty) else { return false };
        active.push(name.to_owned());
        let sized = known_sized(def, defs, active, depth + 1, budget);
        active.pop();
        return sized;
    }
    match ty {
        Ty::Bool
        | Ty::Char
        | Ty::Int { .. }
        | Ty::Float { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Unit
        | Ty::Never
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::Seq { .. }
        | Ty::FnPtr { .. }
        | Ty::FnDef { .. } => true,
        Ty::Array { elem, .. } => known_sized(elem, defs, active, depth + 1, budget),
        Ty::Tuple(fields) => {
            fields.iter().all(|field| known_sized(field, defs, active, depth + 1, budget))
        }
        Ty::Adt { fields, variants, adt_kind: Some(AdtKind::Struct | AdtKind::Union), .. }
            if variants.is_empty() =>
        {
            fields.iter().all(|(_, field)| known_sized(field, defs, active, depth + 1, budget))
        }
        Ty::Adt { variants, adt_kind: Some(AdtKind::Enum), .. } if !variants.is_empty() => {
            variants.iter().all(|variant| {
                variant
                    .fields
                    .iter()
                    .all(|(_, field)| known_sized(field, defs, active, depth + 1, budget))
            })
        }
        _ => false,
    }
}

/// Eligibility is about representation, not proof authority. It does not mint a
/// correspondence, safe-borrow, no-panic, or totality certificate.
fn physical_value(
    ty: &Ty,
    defs: &DatatypeDefs,
    active: &mut Vec<String>,
    depth: usize,
    budget: &mut usize,
) -> bool {
    if spend(depth, budget).is_none() {
        return false;
    }
    if let Some(name) = trust_types::bare_datatype_marker_name(ty) {
        if active.iter().any(|entry| entry == name) {
            return false;
        }
        let Some(def) = trust_types::datatype_marker_definition(defs, ty) else { return false };
        active.push(name.to_owned());
        let eligible = physical_value(def, defs, active, depth + 1, budget);
        active.pop();
        return eligible;
    }
    match ty {
        Ty::Bool | Ty::Char | Ty::PtrSizedInt { .. } | Ty::Unit => true,
        Ty::Int { width: 8 | 16 | 32 | 64 | 128, .. } | Ty::Float { width: 32 | 64 } => true,
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
            // A reference ends the value-layout graph. A bare marker must at
            // least identify a sized physical pointee: otherwise an unknown DST
            // could be incorrectly registered as a thin pointer.
            match inner.as_ref() {
                Ty::Str => true,
                Ty::Slice { elem } => physical_value(elem, defs, active, depth + 1, budget),
                _ => known_sized(inner, defs, &mut Vec::new(), depth + 1, budget),
            }
        }
        Ty::Array { elem, .. } => physical_value(elem, defs, active, depth + 1, budget),
        Ty::Tuple(fields) if fields.is_empty() => true,
        Ty::Adt {
            fields, variants, adt_kind: Some(AdtKind::Struct), layout: Some(layout), ..
        } => {
            variants.is_empty()
                && layout.align.is_power_of_two()
                && layout.size % layout.align == 0
                && layout.field_offsets.len() == fields.len()
                && layout.field_offsets.iter().all(|offset| *offset <= layout.size)
                && fields
                    .iter()
                    .all(|(_, field)| physical_value(field, defs, active, depth + 1, budget))
        }
        Ty::Adt {
            variants,
            adt_kind: Some(AdtKind::Enum),
            faithful_enum_repr: Some(_),
            enum_layout: Some(layout),
            ..
        } => {
            !variants.is_empty()
                && layout.align.is_power_of_two()
                && layout.size % layout.align == 0
                && layout.variant_field_offsets.len() == variants.len()
                && variants.iter().zip(&layout.variant_field_offsets).all(|(variant, offsets)| {
                    offsets.len() == variant.fields.len()
                        && offsets.iter().all(|offset| *offset <= layout.size)
                        && variant.fields.iter().all(|(_, field)| {
                            physical_value(field, defs, active, depth + 1, budget)
                        })
                })
        }
        // No invented layouts for unions, logical sequences, nonempty tuples,
        // generic/compacted markers, callable models, or unknown future types.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::AdtLayoutInfo;

    use super::*;

    fn marker(name: &str) -> Ty {
        Ty::Datatype { name: name.into(), variants: vec![] }
    }

    fn structure(name: &str, fields: Vec<Ty>) -> Ty {
        let count = fields.len();
        let mut ty = Ty::adt(
            name,
            fields.into_iter().enumerate().map(|(i, ty)| (i.to_string(), ty)).collect(),
        );
        if let Ty::Adt { adt_kind, layout, .. } = &mut ty {
            *adt_kind = Some(AdtKind::Struct);
            *layout = Some(Box::new(AdtLayoutInfo {
                size: count as u64 * 8,
                align: 8,
                field_offsets: (0..count as u64).map(|i| i * 8).collect(),
                repr: "c".into(),
            }));
        }
        ty
    }

    #[test]
    fn physical_marker_recovers_complete_definition_and_nested_values() {
        let inner = structure("Inner", vec![Ty::u64()]);
        let outer = structure("Outer", vec![marker("Inner")]);
        let defs = [("Inner".into(), inner.clone()), ("Outer".into(), outer)].into();
        assert_eq!(normalize(&marker("Outer"), &defs), structure("Outer", vec![inner]));
    }

    #[test]
    fn logical_and_missing_or_miskeyed_definitions_stay_opaque() {
        let reference = marker("Value<u8>");
        let logical = Ty::Datatype {
            name: "Value<u8>".into(),
            variants: vec![("Mk".into(), vec![("x".into(), Ty::u8())])],
        };
        for defs in [
            DatatypeDefs::new(),
            [("Value<u8>".into(), structure("Value<u64>", vec![Ty::u64()]))].into(),
            [("Value<u8>".into(), logical.clone())].into(),
            [("Value<u8>".into(), reference.clone())].into(),
        ] {
            assert_eq!(normalize(&reference, &defs), reference);
            assert_eq!(normalize(&logical, &defs), logical);
        }
    }

    #[test]
    fn unions_unstamped_or_incomplete_layouts_and_sequences_stay_opaque() {
        let valid = structure("Value", vec![Ty::u64()]);
        let mut cases = vec![];
        for kind in [None, Some(AdtKind::Union), Some(AdtKind::Enum)] {
            let mut ty = valid.clone();
            if let Ty::Adt { adt_kind, .. } = &mut ty {
                *adt_kind = kind;
            }
            cases.push(ty);
        }
        let mut missing_layout = valid.clone();
        if let Ty::Adt { layout, .. } = &mut missing_layout {
            *layout = None;
        }
        cases.push(missing_layout);
        for bad in [
            AdtLayoutInfo { size: 8, align: 0, field_offsets: vec![0], repr: "c".into() },
            AdtLayoutInfo { size: 8, align: 8, field_offsets: vec![], repr: "c".into() },
            AdtLayoutInfo { size: 8, align: 8, field_offsets: vec![9], repr: "c".into() },
        ] {
            let mut ty = valid.clone();
            if let Ty::Adt { layout, .. } = &mut ty {
                *layout = Some(Box::new(bad));
            }
            cases.push(ty);
        }
        cases
            .push(structure("Value", vec![Ty::Seq { elem: Box::new(Ty::u64()), drop_auth: None }]));
        cases.push(structure("Value", vec![marker("Compacted")]));
        for ty in cases {
            assert_eq!(
                normalize(&marker("Value"), &[("Value".into(), ty)].into()),
                marker("Value")
            );
        }
    }

    #[test]
    fn value_cycles_decline_but_recursive_pointers_keep_wrappers_and_are_idempotent() {
        let direct = structure("Node", vec![marker("Node")]);
        assert_eq!(normalize(&marker("Node"), &[("Node".into(), direct)].into()), marker("Node"));
        let mutual = [
            ("Node".into(), structure("Node", vec![marker("Other")])),
            ("Other".into(), structure("Other", vec![marker("Node")])),
        ]
        .into();
        assert_eq!(normalize(&marker("Node"), &mutual), marker("Node"));
        let node = structure(
            "Node",
            vec![Ty::RawPtr { mutable: false, pointee: Box::new(marker("Node")) }, Ty::u64()],
        );
        let defs = [("Node".into(), node.clone())].into();
        assert_eq!(normalize(&marker("Node"), &defs), node);
        assert_eq!(normalize(&node, &defs), node);
        let borrowed = Ty::Ref { mutable: false, inner: Box::new(marker("Node")) };
        let expanded = normalize(&borrowed, &defs);
        assert_eq!(expanded, Ty::Ref { mutable: false, inner: Box::new(node) });
        assert_eq!(normalize(&expanded, &defs), expanded);
    }

    #[test]
    fn dst_prefix_layout_cannot_license_a_thin_pointer() {
        let dst = structure("Dst", vec![Ty::Str]);
        let outer = structure(
            "Outer",
            vec![Ty::RawPtr { mutable: false, pointee: Box::new(marker("Dst")) }],
        );
        let defs = [("Dst".into(), dst), ("Outer".into(), outer)].into();
        assert_eq!(normalize(&marker("Outer"), &defs), marker("Outer"));
    }

    #[test]
    fn callable_and_wrapper_children_use_the_current_table_without_caching_names() {
        let make = |name: &str, field| [(name.into(), structure(name, vec![field]))].into();
        let input = Ty::FnPtr {
            sig: Box::new(trust_types::FnSig {
                params: vec![Ty::Tuple(vec![marker("Value")])],
                ret: Box::new(marker("Value")),
            }),
        };
        let first = normalize(&input, &make("Value", Ty::u64()));
        let second = normalize(&input, &make("Value", Ty::Bool));
        assert_ne!(first, second);
        assert_eq!(normalize(&input, &DatatypeDefs::new()), input);
        assert_eq!(normalize(&first, &make("Value", Ty::Bool)), first);
    }

    #[test]
    fn expansion_budget_is_fail_closed() {
        let reference = marker("Value");
        let defs = [("Value".into(), structure("Value", vec![Ty::u64()]))].into();
        assert!(expand(&reference, &defs, &mut vec![], 0, &mut 0).is_none());
        let mut budget = MAX_NODES;
        assert!(expand(&reference, &defs, &mut vec![], MAX_DEPTH, &mut budget).is_none());
        let huge = structure("Value", vec![Ty::u64(); MAX_NODES]);
        assert_eq!(normalize(&reference, &[("Value".into(), huge)].into()), reference);
        let siblings = Ty::Tuple(vec![marker("A"), marker("B")]);
        let defs = [
            ("A".into(), structure("A", vec![Ty::u64(); 6000])),
            ("B".into(), structure("B", vec![Ty::u64(); 5000])),
        ]
        .into();
        let first = normalize(&siblings, &defs);
        assert_eq!(first, siblings, "an exhausted later sibling rolls back the whole view");
        assert_eq!(normalize(&first, &defs), first);
    }

    #[test]
    fn wave489_body_view_and_tuple_layouts_view_stay_borrowed_when_no_expandable_marker_occurs() {
        use trust_types::{
            BasicBlock, BlockId, LayoutTarget, LocalDecl, Operand, Place, Projection, Rvalue,
            SourceSpan, Statement, Terminator,
        };

        let value_def = structure("Value", vec![Ty::u64()]);
        let logical_def = Ty::Datatype {
            name: "LogicalOnly".into(),
            variants: vec![("Mk".into(), vec![("x".into(), marker("Value"))])],
        };
        let defs: DatatypeDefs =
            [("Value".into(), value_def.clone()), ("LogicalOnly".into(), logical_def.clone())]
                .into();
        let span = SourceSpan {
            file: "wave489.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        };
        let mut body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: marker("Missing"), name: None },
                LocalDecl { index: 2, ty: logical_def, name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(0)), Ty::u64()),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: defs.clone(),
        };

        let borrowed = body_view(&body);
        assert!(
            matches!(borrowed, Cow::Borrowed(ptr) if std::ptr::eq(ptr, &body)),
            "body without expandable physical markers must stay Cow::Borrowed"
        );

        // Introducing a nested expandable marker inside an OpaqueCast projection must trigger Owned.
        body.blocks[0].stmts.push(Statement::PlaceMention(Place {
            local: 1,
            projections: vec![Projection::OpaqueCast(Ty::Tuple(vec![marker("Value")]))],
        }));
        let owned = body_view(&body);
        assert!(matches!(owned, Cow::Owned(_)), "expandable marker inside projection must rewrite");
        let Statement::PlaceMention(rewritten_place) = &owned.blocks[0].stmts[1] else {
            panic!("expected PlaceMention");
        };
        assert_eq!(
            *rewritten_place,
            Place {
                local: 1,
                projections: vec![Projection::OpaqueCast(Ty::Tuple(vec![value_def.clone()]))],
            }
        );

        let target = Some(LayoutTarget {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            little_endian: true,
        });
        let scalar_row = TupleLayoutInfo {
            tuple: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
            size: 16,
            align: 8,
            field_offsets: vec![0, 8],
            field_sizes: vec![8, 1],
            field_aligns: vec![8, 1],
        };
        let scalar_layouts = TupleLayouts { target: target.clone(), entries: vec![scalar_row.clone()] };
        let borrowed_layouts = tuple_layouts_view(&scalar_layouts, &defs);
        assert!(
            matches!(borrowed_layouts, Cow::Borrowed(ptr) if std::ptr::eq(ptr, &scalar_layouts)),
            "single coherent scalar tuple layout must stay Cow::Borrowed"
        );

        // Targetless or incoherent rows must still go through TupleLayouts::from_rows refusal.
        let targetless = TupleLayouts { target: None, entries: vec![scalar_row] };
        assert!(tuple_layouts_view(&targetless, &defs).is_empty());

        let marker_layouts = TupleLayouts {
            target,
            entries: vec![TupleLayoutInfo {
                tuple: Ty::Tuple(vec![marker("Value")]),
                size: 8,
                align: 8,
                field_offsets: vec![0],
                field_sizes: vec![8],
                field_aligns: vec![8],
            }],
        };
        let expanded_layouts = tuple_layouts_view(&marker_layouts, &defs);
        assert!(matches!(expanded_layouts, Cow::Owned(_)));
        assert_eq!(expanded_layouts.entries[0].tuple, Ty::Tuple(vec![value_def]));
    }
}
