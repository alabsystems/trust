// trust_vcgen/rvalue_safety.rs: Safety VCs for Rvalue::Discriminant, Aggregate, Ref, and Len
//
// The forward VC generation pass previously skipped several Rvalue
// variants. This module generates verification conditions for:
//
// - Rvalue::Discriminant(place): Verifies the place holds an enum/ADT type.
//   Reading a discriminant from a non-enum is undefined behavior.
//
// - Rvalue::Aggregate(AggregateKind::Array, operands): Verifies the operand
//   count matches the declared array length when the assignment target has
//   an Array type.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AggregateKind, BasicBlock, Formula, ObligationRecord, Operand, Projection, Rvalue, Sort,
    SourceSpan, Ty, VcKind, VerifiableFunction, VerificationCondition,
};

use crate::{
    local_ty_ref, operand_to_formula, place_to_var_name, slice_len_formula, step_place_ty_cow,
};

/// Check an rvalue for Discriminant and Aggregate safety violations.
///
/// Called from `generate_vcs()` for each `Statement::Assign` in the forward pass.
pub(crate) fn check_rvalue_safety(
    func: &VerifiableFunction,
    _block: &BasicBlock,
    rvalue: &Rvalue,
    dest_ty: Option<&Ty>,
    stmt_span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    match rvalue {
        // Discriminant read — place must hold an enum/ADT type.
        Rvalue::Discriminant(place) => {
            let place_name = place_to_var_name(func, place);
            // verifier-perf: borrowed resolve — this is a pure variant inspection
            // (is the discriminant read on an ADT/Datatype?), never a move, so never
            // clone the (possibly fat recursive-ADT) declared root.
            let resolved_ty = crate::place_ty_cow(func, place);

            // If the type resolves to a concrete non-ADT (which models enums),
            // the discriminant read is a definite violation. when the
            // type is UNRESOLVABLE (`None`) we must fail open to Unknown rather
            // than emit a definite-violation VC — an unresolvable nested-enum
            // payload place is not evidence of a non-enum read, and emitting here
            // is a Goal-1 false-fail. Only `Some(non-Adt)` is a genuine violation.
            //
            // SOUNDNESS (Lever A): a `Ty::Datatype` is the modeled-enum form the
            // recursive-ADT lowering produces (a by-name datatype reference for a
            // compacted `Expr`/`Level`/`Name` field, or a full variant list at the
            // definition). A `Discriminant` read on a modeled enum is VALID, not a
            // violation, so `Ty::Datatype` must be treated exactly like `Ty::Adt`
            // here — otherwise the datatype modeling would FALSE-FAIL every correct
            // discriminant read through a compacted enum field (a Goal-1 regression,
            // exactly the false-refutation the benchmark gate forbids). Only a
            // genuine non-enum scalar (`Some(t)` that is neither `Ty::Adt` nor
            // `Ty::Datatype`) remains a real invalid-discriminant violation.
            // Trust: piece #13 step-2 (safe-async data-safety) — a `Discriminant`
            // read on a COROUTINE frame (`_ = discriminant((*self))`) is the
            // resume-STATE selector read, a VALID compiler-generated read, NOT an
            // invalid-discriminant-on-a-scalar violation. The frame is modeled
            // opaquely (`Ty::Coroutine`, no fields), and its state selector feeds no
            // data obligation (it is havoc'd on the native lane and drives only the
            // resume-state `SwitchInt`). Treat `Ty::Coroutine` exactly like
            // `Ty::Adt`/`Ty::Datatype` here — otherwise every `async fn` / coroutine
            // resume body would FALSE-FAIL its state-discriminant read (a Goal-1
            // false refutation, the exact regression this predicate forbids for
            // modeled enums). Only a genuine non-enum scalar remains a real
            // invalid-discriminant violation.
            let definitely_not_adt = matches!(
                resolved_ty.as_deref(),
                Some(t) if !matches!(t, Ty::Adt { .. } | Ty::Datatype { .. } | Ty::Coroutine { .. })
            );
            if definitely_not_adt {
                // The discriminant is read on a type that is not an ADT/enum.
                // Formula: the place's "type tag" != ADT_TAG, which is trivially
                // satisfiable, meaning a solver will confirm the violation.
                let type_tag_var = Formula::Var(format!("{place_name}__type_tag"), Sort::Int);
                // ADT_TAG sentinel: we use -1 as a sentinel for "is an ADT"
                let adt_sentinel = Formula::Int(-1);
                let not_adt = Formula::Not(Box::new(Formula::Eq(
                    Box::new(type_tag_var),
                    Box::new(adt_sentinel),
                )));
                vcs.push(VerificationCondition {
                    kind: VcKind::InvalidDiscriminant { place_name },
                    function: func.name.as_str().into(),
                    location: stmt_span.clone(),
                    formula: not_adt,
                    contract_metadata: None,
                    obligation: None,
                });
            }
        }

        // Array aggregate — operand count must match array length.
        Rvalue::Aggregate(AggregateKind::Array, operands) => {
            if let Some(Ty::Array { len, .. }) = dest_ty {
                let expected = *len as usize;
                let actual = operands.len();
                if expected != actual {
                    // Formula: expected_len != actual_len (trivially SAT = definite violation)
                    let expected_f = Formula::Int(expected as i128);
                    let actual_f = Formula::Int(actual as i128);
                    let mismatch = Formula::Not(Box::new(Formula::Eq(
                        Box::new(expected_f),
                        Box::new(actual_f),
                    )));
                    vcs.push(VerificationCondition {
                        kind: VcKind::AggregateArrayLengthMismatch { expected, actual },
                        function: func.name.as_str().into(),
                        location: stmt_span.clone(),
                        formula: mismatch,
                        contract_metadata: None,
                        obligation: None,
                    });
                }
            }
        }

        // Synthetic TrustIr often represents `arr[i]`, `arr[2]`, and `slice[a..b]`
        // directly as a projection load rather than as a native BoundsCheck
        // assert followed by the load. Emit the same safety obligation here so
        // those functions still reach the router with a bounds VC.
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            check_direct_projection_load(func, place, stmt_span, vcs);
        }

        // Reference-side index projections. `&arr[i]`, `&mut arr[i]`,
        // `&raw const arr[i]` / `&raw mut arr[i]`, and the compiler-inserted
        // `CopyForDeref(arr[i])` all dereference/borrow the indexed element, so
        // an out-of-bounds index is just as much UB as a read. Previously these
        // sites carried ZERO bounds check, silently reporting an out-of-bounds
        // borrow as safe. Reuse the same projection-load obligation builder the
        // read path uses (same `index < len` formula, same guard/precondition
        // discharge), so a guarded `if i < arr.len()` proves and an unguarded
        // index fails.
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) | Rvalue::CopyForDeref(place) => {
            check_direct_projection_load(func, place, stmt_span, vcs);
        }

        _ => {}
    }
}

/// Bounds-check the destination `place` of a `Statement::Assign`.
///
/// `arr[i] = v` carries the `Index(i)` projection on the assignment's
/// *destination* place, not on the rvalue, so the read/rvalue-driven
/// [`check_rvalue_safety`] never inspects it. Without this, an out-of-bounds
/// STORE was reported safe. We reuse the exact same projection-load obligation
/// builder the read path uses, so the emitted `index < len` obligation is
/// discharged by the same guard/precondition machinery (a guarded
/// `if i < arr.len() { arr[i] = v }` proves; a bare `arr[i] = v` fails).
pub(crate) fn check_place_index_bounds(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    stmt_span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    check_direct_projection_load(func, place, stmt_span, vcs);
}

/// Whether `place` carries an Index/ConstantIndex/Subslice projection that
/// needs a bounds obligation. Used both to recognize store-side index
/// destinations and to gate the native-`BoundsCheck`-assert suppression so the
/// reference/store sites mirror the read path's skip behavior.
pub(crate) fn place_needs_bounds_check(place: &trust_types::Place) -> bool {
    place.projections.iter().any(|projection| {
        matches!(
            projection,
            Projection::Index(_) | Projection::ConstantIndex { .. } | Projection::Subslice { .. }
        )
    })
}

pub(crate) fn is_direct_projection_load(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => place_needs_bounds_check(place),
        _ => false,
    }
}

fn check_direct_projection_load(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    stmt_span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    // verifier-perf: walk the declared type by REFERENCE (no fat-root clone). Each VC
    // builder takes `&Ty` and the projection step borrows the subtree (only the synthetic
    // `Subslice`/`OpaqueCast` steps allocate); the fat recursive-ADT root is never cloned.
    use std::borrow::Cow;
    let Some(mut ty) = local_ty_ref(func, place.local).map(Cow::Borrowed) else {
        return;
    };
    let mut prefix = trust_types::Place::local(place.local);

    for projection in &place.projections {
        match projection {
            Projection::Index(index_local) => {
                if let Some(vc) =
                    index_projection_vc(func, &prefix, ty.as_ref(), *index_local, stmt_span)
                {
                    vcs.push(vc);
                }
            }
            Projection::ConstantIndex { offset, min_length, from_end } => {
                if let Some(vc) = constant_index_projection_vc(
                    func,
                    &prefix,
                    ty.as_ref(),
                    *offset,
                    *min_length,
                    *from_end,
                    stmt_span,
                ) {
                    vcs.push(vc);
                }
            }
            Projection::Subslice { from, to, from_end } => {
                if let Some(vc) = subslice_projection_vc(
                    func,
                    &prefix,
                    ty.as_ref(),
                    *from,
                    *to,
                    *from_end,
                    stmt_span,
                ) {
                    vcs.push(vc);
                }
            }
            _ => {}
        }

        let Some(next_ty) = step_place_ty_cow(ty, projection) else {
            return;
        };
        prefix.projections.push(projection.clone());
        ty = next_ty;
    }
}

fn index_projection_vc(
    func: &VerifiableFunction,
    collection: &trust_types::Place,
    collection_ty: &Ty,
    index_local: usize,
    stmt_span: &SourceSpan,
) -> Option<VerificationCondition> {
    let len = collection_len_formula(func, collection, collection_ty)?;
    let index_place = trust_types::Place::local(index_local);
    let index_operand = Operand::Copy(index_place);
    let index_ty = crate::operand_ty_cow(func, &index_operand);
    let index = operand_to_formula(func, &index_operand);
    let violation = index_bounds_violation(index, index_ty.as_deref(), len);

    Some(VerificationCondition {
        kind: projection_vc_kind(&Projection::Index(index_local), collection_ty),
        function: func.name.as_str().into(),
        location: stmt_span.clone(),
        // Trust (bounds ARM, GAP 1): seed the authenticated-obligation record from the
        // raw violation the emitter is ALREADY building — the atomic bounds core
        // (`Ge(i, len)` unsigned, or `Or([Lt(i,0), Ge(i,len)])` signed). No wrappers
        // yet: the SEPARATE rvalue pipeline (`generate_v2_rvalue_safety_vcs_impl`)
        // appends every wrapper it applies (yield facts, preconditions, path guards,
        // semantic guards) so the stored `{body, wrappers}` replays to `formula`.
        // Bounds is payload-free for subject/width (the consumer reads index+len from
        // the body, cross-checked structurally, not against a MIR-implied width).
        formula: violation.clone(),
        contract_metadata: None,
        obligation: Some(ObligationRecord {
            body: violation,
            wrappers: Vec::new(),
            subject: None,
            width: None,
        }),
    })
}

fn constant_index_projection_vc(
    func: &VerifiableFunction,
    collection: &trust_types::Place,
    collection_ty: &Ty,
    offset: usize,
    min_length: usize,
    from_end: bool,
    stmt_span: &SourceSpan,
) -> Option<VerificationCondition> {
    let len = collection_len_formula(func, collection, collection_ty)?;
    let mut violations = vec![Formula::Le(
        Box::new(len.clone()),
        Box::new(Formula::Int(i128::try_from(offset).ok()?)),
    )];
    if min_length > 0 {
        violations.push(Formula::Lt(
            Box::new(len),
            Box::new(Formula::Int(i128::try_from(min_length).ok()?)),
        ));
    }

    let violation = any_violation(violations);
    Some(VerificationCondition {
        kind: projection_vc_kind(
            &Projection::ConstantIndex { offset, min_length, from_end },
            collection_ty,
        ),
        function: func.name.as_str().into(),
        location: stmt_span.clone(),
        // Trust (bounds ARM, GAP 1): record the raw violation as the body; the rvalue
        // pipeline appends the wrappers it applies (see `index_projection_vc`).
        formula: violation.clone(),
        contract_metadata: None,
        obligation: Some(ObligationRecord {
            body: violation,
            wrappers: Vec::new(),
            subject: None,
            width: None,
        }),
    })
}

fn subslice_projection_vc(
    func: &VerifiableFunction,
    collection: &trust_types::Place,
    collection_ty: &Ty,
    from: usize,
    to: usize,
    from_end: bool,
    stmt_span: &SourceSpan,
) -> Option<VerificationCondition> {
    let len = collection_len_formula(func, collection, collection_ty)?;
    let from_f = Formula::Int(i128::try_from(from).ok()?);
    let to_f = Formula::Int(i128::try_from(to).ok()?);
    let violation = if from_end {
        Formula::Gt(Box::new(Formula::Add(Box::new(from_f), Box::new(to_f))), Box::new(len))
    } else {
        Formula::Or(vec![
            Formula::Gt(Box::new(from_f), Box::new(to_f.clone())),
            Formula::Gt(Box::new(to_f), Box::new(len)),
        ])
    };

    Some(VerificationCondition {
        kind: VcKind::SliceBoundsCheck,
        function: func.name.as_str().into(),
        location: stmt_span.clone(),
        // Trust (bounds ARM, GAP 1): record the raw subslice violation as the body; the
        // rvalue pipeline appends the wrappers it applies (see `index_projection_vc`).
        formula: violation.clone(),
        contract_metadata: None,
        obligation: Some(ObligationRecord {
            body: violation,
            wrappers: Vec::new(),
            subject: None,
            width: None,
        }),
    })
}

fn projection_vc_kind(projection: &Projection, collection_ty: &Ty) -> VcKind {
    if matches!(projection, Projection::Subslice { .. })
        || matches!(collection_ty, Ty::Slice { .. })
    {
        VcKind::SliceBoundsCheck
    } else {
        VcKind::IndexOutOfBounds
    }
}

pub(crate) fn collection_len_formula(
    func: &VerifiableFunction,
    collection: &trust_types::Place,
    collection_ty: &Ty,
) -> Option<Formula> {
    match collection_ty {
        Ty::Array { len, .. } => Some(Formula::Int(i128::from(*len))),
        // Trust: piece #7a — a const-generic array `[T; N]` yields the per-param
        // length symbol so `index_bounds_violation` builds `i >= N ∨ i < 0`. With
        // no guard this is SAT (REFUTED — an unguarded const-generic index IS
        // OOB-capable); under a guard `i < N` (whose `N` shares the SAME symbol)
        // it is UNSAT (PROVED). SOUNDNESS: keyed on the param identity, so an
        // index on `[T; M]` is NOT dischargeable by a guard on `N` (M != N).
        Ty::SymArray { len_sym, .. } => Some(crate::sym_array_len_formula(len_sym)),
        Ty::Slice { .. } => {
            slice_len_formula(func, &Operand::Copy(slice_metadata_place(func, collection)))
        }
        Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Slice { .. }) => {
            slice_len_formula(func, &Operand::Copy(collection.clone()))
        }
        _ => None,
    }
}

fn slice_metadata_place(
    func: &VerifiableFunction,
    collection: &trust_types::Place,
) -> trust_types::Place {
    let Some(Projection::Deref) = collection.projections.last() else {
        return collection.clone();
    };

    let mut base = collection.clone();
    base.projections.pop();
    if matches!(
        crate::place_ty_cow(func, &base).as_deref(),
        Some(Ty::Ref { inner, .. }) if matches!(inner.as_ref(), Ty::Slice { .. })
    ) {
        base
    } else {
        collection.clone()
    }
}

pub(crate) fn index_bounds_violation(
    index: Formula,
    index_ty: Option<&Ty>,
    len: Formula,
) -> Formula {
    if index_ty.is_some_and(Ty::is_signed) {
        Formula::Or(vec![
            Formula::Lt(Box::new(index.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(index), Box::new(len)),
        ])
    } else {
        Formula::Ge(Box::new(index), Box::new(len))
    }
}

fn any_violation(mut violations: Vec<Formula>) -> Formula {
    if violations.len() == 1 {
        violations.pop().expect("one violation")
    } else {
        Formula::Or(violations)
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    /// Helper: build a function with a Discriminant rvalue on a non-ADT local.
    fn discriminant_on_non_enum() -> VerifiableFunction {
        VerifiableFunction {
            name: "disc_non_enum".to_string(),
            def_path: "test::disc_non_enum".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) }, // not an enum
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) }, // discriminant dest
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a function with a Discriminant rvalue on an ADT local.
    fn discriminant_on_enum() -> VerifiableFunction {
        VerifiableFunction {
            name: "disc_enum".to_string(),
            def_path: "test::disc_enum".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Adt { adt_kind: None, layout: None, 
                            name: "MyEnum".into(),
                            fields: vec![("discriminant".into(), Ty::u32())],
                            variants: Vec::new(),
                            disc_index_safe: false,
                            faithful_enum_repr: None, enum_layout: None, },
                        name: Some("e".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_discriminant_on_non_enum_generates_vc() {
        let func = discriminant_on_non_enum();
        let vcs = crate::generate_vcs(&func);
        let disc_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::InvalidDiscriminant { .. }))
            .collect();
        assert_eq!(
            disc_vcs.len(),
            1,
            "Discriminant on non-enum should produce exactly 1 InvalidDiscriminant VC"
        );
        if let VcKind::InvalidDiscriminant { place_name } = &disc_vcs[0].kind {
            assert_eq!(place_name, "x", "VC should reference the place name");
        }
    }

    #[test]
    fn test_discriminant_on_enum_no_vc() {
        let func = discriminant_on_enum();
        let vcs = crate::generate_vcs(&func);
        let disc_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::InvalidDiscriminant { .. }))
            .collect();
        assert!(
            disc_vcs.is_empty(),
            "Discriminant on ADT should not produce InvalidDiscriminant VC"
        );
    }

    /// Helper: build a function with an Array aggregate where operand count
    /// mismatches the declared array length.
    fn array_aggregate_mismatch() -> VerifiableFunction {
        VerifiableFunction {
            name: "arr_mismatch".to_string(),
            def_path: "test::arr_mismatch".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    // _0: return type
                    LocalDecl {
                        index: 0,
                        ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 },
                        name: None,
                    },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        // Only 2 operands for a [u32; 3] array — mismatch!
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Array,
                            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a function with a matching Array aggregate.
    fn array_aggregate_matching() -> VerifiableFunction {
        VerifiableFunction {
            name: "arr_match".to_string(),
            def_path: "test::arr_match".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Array { elem: Box::new(Ty::u32()), len: 2 },
                        name: None,
                    },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Array,
                            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Array { elem: Box::new(Ty::u32()), len: 2 },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_array_aggregate_mismatch_generates_vc() {
        let func = array_aggregate_mismatch();
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert_eq!(arr_vcs.len(), 1, "Array aggregate with mismatched length should produce 1 VC");
        if let VcKind::AggregateArrayLengthMismatch { expected, actual } = &arr_vcs[0].kind {
            assert_eq!(*expected, 3);
            assert_eq!(*actual, 2);
        }
    }

    #[test]
    fn test_array_aggregate_matching_no_vc() {
        let func = array_aggregate_matching();
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert!(arr_vcs.is_empty(), "Array aggregate with matching length should not produce VC");
    }

    #[test]
    fn test_discriminant_vc_is_l0_safety() {
        let func = discriminant_on_non_enum();
        let vcs = crate::generate_vcs(&func);
        let disc_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::InvalidDiscriminant { .. }))
            .collect();
        assert_eq!(disc_vcs.len(), 1);
        assert_eq!(
            disc_vcs[0].kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "InvalidDiscriminant should be L0 safety"
        );
    }

    #[test]
    fn test_aggregate_mismatch_vc_is_l0_safety() {
        let func = array_aggregate_mismatch();
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert_eq!(arr_vcs.len(), 1);
        assert_eq!(
            arr_vcs[0].kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "AggregateArrayLengthMismatch should be L0 safety"
        );
    }

    #[test]
    fn test_tuple_aggregate_no_vc() {
        // Tuple aggregates should not produce array-length VCs
        let func = VerifiableFunction {
            name: "tuple_agg".to_string(),
            def_path: "test::tuple_agg".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Bool(true)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert!(arr_vcs.is_empty(), "Tuple aggregate should not produce array-length VC");
    }
}

// Trust: piece #7a — symbolic const-generic array length.
#[cfg(test)]
mod sym_array_tests {
    use trust_types::{
        BasicBlock, BlockId, ConstLen, ConstValue, Formula, LocalDecl, Operand, Place, Sort,
        SourceSpan, Terminator, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    /// Build a trivial function whose local `_1` has a const-generic array type
    /// `[u8; N]` (`Ty::SymArray`), for the `collection_len_formula` tests.
    fn sym_array_func(len_sym: ConstLen) -> VerifiableFunction {
        VerifiableFunction {
            name: "sym_array".to_string(),
            def_path: "test::sym_array".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u8(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::SymArray { elem: Box::new(Ty::u8()), len_sym },
                        name: Some("a".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u8(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn sym_array_collection_len_is_per_param_symbol() {
        let func = sym_array_func(ConstLen { index: 1, name: "N".to_string() });
        let place = Place::local(1);
        let ty = func.body.locals[1].ty.clone();
        let len = collection_len_formula(&func, &place, &ty).expect("SymArray must yield a length");
        // The length is the canonical per-param symbol, NOT a concrete Int and NOT
        // a `__slice_len` (so `conjoin_slice_len_bounds` cannot attach a bound).
        assert_eq!(len, Formula::var("__trust_constparam_1_N", Sort::Int));
    }

    #[test]
    fn distinct_const_params_get_distinct_length_symbols() {
        // The M==N collision defense at the unit level (INV-1), independent of the
        // solver: two distinct const-params must render to DISTINCT SMT var names.
        let m_func = sym_array_func(ConstLen { index: 0, name: "M".to_string() });
        let n_func = sym_array_func(ConstLen { index: 1, name: "N".to_string() });
        let m = collection_len_formula(&m_func, &Place::local(1), &m_func.body.locals[1].ty)
            .expect("M length");
        let n = collection_len_formula(&n_func, &Place::local(1), &n_func.body.locals[1].ty)
            .expect("N length");
        assert_ne!(
            m, n,
            "distinct const-params must NOT collapse to one symbol (M==N false proof)"
        );
    }

    #[test]
    fn const_param_value_operand_matches_array_length_symbol() {
        // The linchpin: the VALUE `N` read as an operand must render the SAME
        // string the array length uses, so a guard `i < N` shares the SMT term.
        let func = sym_array_func(ConstLen { index: 1, name: "N".to_string() });
        let value_n = Operand::Constant(ConstValue::ConstParam {
            index: 1,
            name: "N".to_string(),
            width: 64,
            signed: false,
        });
        let value_f = crate::operand_to_formula(&func, &value_n);
        assert_eq!(value_f, Formula::var("__trust_constparam_1_N", Sort::Int));
        // And it is byte-identical to the length symbol.
        let len = collection_len_formula(&func, &Place::local(1), &func.body.locals[1].ty).unwrap();
        assert_eq!(value_f, len, "guard value N and array length N must be the SAME term");
    }
}
