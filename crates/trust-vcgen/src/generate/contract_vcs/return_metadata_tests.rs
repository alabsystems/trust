//! Exact typed metadata-return regressions. These exercise the body-aware
//! contract generator, not a general license to encode `PtrMetadata` in CHC.
//! A pin must describe the pointer value actually read on this return edge;
//! element mutation preserves length, but reseating/escaping the pointer does
//! not. Unsupported metadata must not borrow authority from another `_0` write.

use trust_types::{
    BasicBlock, BlockId, ConstValue, ContractKind, Formula, LocalDecl, Operand, Place, Projection,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnOp, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

use super::{formula_has_return_slot_pin, generate_v2_contract_vcs_impl};

fn slice() -> Ty {
    Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }
}

fn reference(inner: Ty, mutable: bool) -> Ty {
    Ty::Ref { inner: Box::new(inner), mutable }
}

fn raw(pointee: Ty, mutable: bool) -> Ty {
    Ty::RawPtr { pointee: Box::new(pointee), mutable }
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn metadata(local: usize, moved: bool) -> Rvalue {
    let place = Place::local(local);
    Rvalue::UnaryOp(
        UnOp::PtrMetadata,
        if moved { Operand::Move(place) } else { Operand::Copy(place) },
    )
}

fn length(func: &VerifiableFunction, local: usize) -> Formula {
    match crate::ptr_metadata_model(func, &Operand::Copy(Place::local(local))) {
        crate::PtrMetadataModel::Length(length) => length,
        other => panic!("expected a typed slice/str metadata term, got {other:?}"),
    }
}

fn result_eq(value: Formula) -> Formula {
    Formula::Eq(Box::new(Formula::var("_0", Sort::Int)), Box::new(value))
}

fn subject(pointer: Ty, moved: bool, predecessor: bool) -> VerifiableFunction {
    let mut func = VerifiableFunction {
        name: "metadata_return".into(),
        def_path: "test::metadata_return".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: pointer.clone(), name: Some("xs".into()) },
                LocalDecl { index: 2, ty: pointer, name: Some("ys".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(0, metadata(1, moved))],
                terminator: if predecessor {
                    Terminator::Goto(BlockId(1))
                } else {
                    Terminator::Return
                },
            }],
            arg_count: 2,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    if predecessor {
        func.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });
    }
    func.postconditions = vec![result_eq(length(&func, 1))];
    func
}

fn emit(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    crate::validate_function(func).expect("the control must remain well-formed Trust MIR");
    generate_v2_contract_vcs_impl(func, None)
}

/// Only unconditional conjuncts are body pins. An equality inside `Not(post)`
/// must never satisfy this test.
fn spine_pins_value(formula: &Formula, expected: &Formula) -> bool {
    match formula {
        Formula::And(parts) => parts.iter().any(|part| spine_pins_value(part, expected)),
        Formula::Eq(lhs, rhs) => {
            matches!(lhs.as_ref(), Formula::Var(name, Sort::Int)
                if name.as_str() == "_0" || name.as_str().starts_with("_0#"))
                && rhs.as_ref() == expected
        }
        _ => false,
    }
}

fn pinned_post(func: &VerifiableFunction, source: usize) -> VerificationCondition {
    let vcs = emit(func);
    assert_eq!(
        vcs.len(),
        1,
        "one body-aware contract row, with no hidden unsupported residue: {vcs:?}"
    );
    let vc = vcs.into_iter().next().unwrap();
    assert!(matches!(vc.kind, VcKind::Postcondition), "{vc:?}");
    assert!(formula_has_return_slot_pin(&vc.formula), "{vc:?}");
    assert!(spine_pins_value(&vc.formula, &length(func, source)), "{vc:?}");
    vc
}

fn ay(vc: &VerificationCondition, proved: bool) {
    // Keep the real Postcondition kind: changing lanes to obtain a favorable
    // solver answer would not measure the return-contract path.
    assert!(matches!(vc.kind, VcKind::Postcondition));
    let result = crate::test_router::shipped_vc_clock_router().verify_all(std::slice::from_ref(vc));
    assert_eq!(result.len(), 1, "{result:?}");
    if proved {
        assert!(matches!(&result[0].1, VerificationResult::Proved { .. }), "{result:?}");
    } else {
        assert!(matches!(&result[0].1, VerificationResult::Failed { .. }), "{result:?}");
    }
}

fn refused(func: &VerifiableFunction) {
    let vcs = emit(func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "unsupported metadata must not become a refutable postcondition, even with another pin: {vcs:?}"
    );
    assert!(
        vcs.iter().any(|vc| matches!(&vc.kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "SpecUnverifiable")),
        "the missing relation must remain a visible obligation: {vcs:?}"
    );
}

fn append_local(func: &mut VerifiableFunction, ty: Ty) -> usize {
    let index = func.body.locals.len();
    func.body.locals.push(LocalDecl { index, ty, name: None });
    index
}

fn call(dest: usize, target: usize, args: Vec<Operand>) -> Terminator {
    Terminator::Call {
        func: "test::unmodeled_effect".into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Unreachable,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("test::unmodeled_effect"),
    }
}

#[test]
fn whole_slice_str_and_raw_parameter_returns_pin_copy_and_move_on_each_edge_shape() {
    for pointer in [
        reference(slice(), false),
        reference(slice(), true),
        reference(Ty::Str, false),
        raw(slice(), false),
        raw(slice(), true),
        raw(Ty::Str, false),
    ] {
        for moved in [false, true] {
            for predecessor in [false, true] {
                pinned_post(&subject(pointer.clone(), moved, predecessor), 1);
            }
        }
    }
}

#[test]
fn exact_metadata_postcondition_and_its_negation_discriminate_in_actual_ay() {
    for moved in [false, true] {
        for predecessor in [false, true] {
            let mut func = subject(reference(slice(), false), moved, predecessor);
            ay(&pinned_post(&func, 1), true);
            func.postconditions[0] = Formula::Not(Box::new(func.postconditions[0].clone()));
            ay(&pinned_post(&func, 1), false);
        }
    }
}

#[test]
fn pointee_element_stores_before_and_after_metadata_read_preserve_length() {
    for after in [false, true] {
        let mut func = subject(reference(slice(), true), false, false);
        func.preconditions.push(Formula::Ge(Box::new(length(&func, 1)), Box::new(Formula::Int(1))));
        let store = Statement::Assign {
            place: Place {
                local: 1,
                projections: vec![
                    Projection::Deref,
                    Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
                ],
            },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))),
            span: SourceSpan::default(),
        };
        func.body.blocks[0].stmts.insert(usize::from(after), store);
        ay(&pinned_post(&func, 1), true);
    }
}

#[test]
fn pointee_reborrows_do_not_count_as_pointer_metadata_reseats() {
    for raw_borrow in [false, true] {
        for after in [false, true] {
            let mut func = subject(reference(slice(), true), false, false);
            let dest = append_local(
                &mut func,
                if raw_borrow { raw(slice(), true) } else { reference(slice(), true) },
            );
            let pointee = Place { local: 1, projections: vec![Projection::Deref] };
            let borrow = if raw_borrow {
                Rvalue::AddressOf(true, pointee)
            } else {
                Rvalue::Ref { mutable: true, place: pointee }
            };
            func.body.blocks[0].stmts.insert(usize::from(after), assign(dest, borrow));
            ay(&pinned_post(&func, 1), true);
        }
    }
}

#[test]
fn pointer_root_reseats_before_or_after_metadata_read_are_refused() {
    for predecessor in [false, true] {
        for after in [false, true] {
            let mut func = subject(reference(slice(), false), false, predecessor);
            let reseat = assign(1, Rvalue::Use(Operand::Copy(Place::local(2))));
            if predecessor && after {
                func.body.blocks[1].stmts.push(reseat);
            } else {
                func.body.blocks[0].stmts.insert(usize::from(after), reseat);
            }
            refused(&func);
        }
    }
}

#[test]
fn metadata_refusal_precedes_the_reassigned_clause_parameter_shortcut() {
    let mut func = subject(reference(slice(), false), false, false);
    let count = append_local(&mut func, Ty::usize());
    func.body.locals[count].name = Some("count".into());
    func.body.arg_count = count;
    // This clause mentions both result and an ordinary parameter. The existing
    // mutated-parameter shortcut runs before per-edge formula assembly; it
    // must not bypass the visible refusal of this unsupported metadata return.
    func.postconditions = vec![result_eq(Formula::var("count", Sort::Int))];
    func.body.blocks[0].stmts.push(assign(1, Rvalue::Use(Operand::Copy(Place::local(2)))));
    func.body.blocks[0]
        .stmts
        .push(assign(count, Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64)))));
    refused(&func);
}

#[test]
fn mutable_or_raw_borrows_of_pointer_root_are_refused() {
    for borrow_kind in 0..3 {
        for after in [false, true] {
            let pointer = reference(slice(), true);
            let mut func = subject(pointer.clone(), false, false);
            let alias_ty = if borrow_kind == 0 {
                reference(pointer, true)
            } else {
                raw(pointer, borrow_kind == 2)
            };
            let dest = append_local(&mut func, alias_ty);
            let borrow = if borrow_kind == 0 {
                Rvalue::Ref { mutable: true, place: Place::local(1) }
            } else {
                Rvalue::AddressOf(borrow_kind == 2, Place::local(1))
            };
            func.body.blocks[0].stmts.insert(usize::from(after), assign(dest, borrow));
            refused(&func);
        }
    }
}

#[test]
fn call_destination_cannot_reseat_the_metadata_source() {
    let mut func = subject(reference(slice(), false), false, true);
    func.body.blocks[1].stmts = std::mem::take(&mut func.body.blocks[0].stmts);
    func.body.blocks[0].terminator = call(1, 1, vec![]);
    refused(&func);
}

#[test]
fn escaped_mutable_pointer_alias_does_not_gain_entry_length_authority() {
    let pointer = reference(slice(), true);
    let mut func = subject(pointer.clone(), false, true);
    let alias = append_local(&mut func, reference(pointer, true));
    let unit = append_local(&mut func, Ty::Unit);
    func.body.blocks[1].stmts = std::mem::take(&mut func.body.blocks[0].stmts);
    func.body.blocks[0]
        .stmts
        .push(assign(alias, Rvalue::Ref { mutable: true, place: Place::local(1) }));
    func.body.blocks[0].terminator = call(unit, 1, vec![Operand::Move(Place::local(alias))]);
    refused(&func);
}

#[test]
fn metadata_identity_uses_exact_local_not_duplicate_debug_name() {
    for duplicate_name in [false, true] {
        let mut func = subject(reference(slice(), false), false, false);
        if duplicate_name {
            func.body.locals[2].name = Some("xs".into());
        }
        let first = length(&func, 1);
        let second = length(&func, 2);
        assert_ne!(first, second, "two pointer parameters must retain different identities");
        func.body.blocks[0].stmts[0] = assign(0, metadata(2, false));
        func.postconditions = vec![result_eq(second.clone())];
        ay(&pinned_post(&func, 2), true);
        func.postconditions = vec![result_eq(first.clone())];
        let vc = pinned_post(&func, 2);
        assert!(!spine_pins_value(&vc.formula, &first), "{vc:?}");
        ay(&vc, false);
    }
}

#[test]
fn scalar_debug_name_cannot_impersonate_slice_length() {
    let mut func = subject(reference(slice(), false), false, false);
    let scalar = append_local(&mut func, Ty::usize());
    func.body.locals[scalar].name = Some("xs__slice_len".into());
    func.body.arg_count = scalar;
    let scalar_name = crate::place_to_var_name(&func, &Place::local(scalar));
    let scalar_value = Formula::var_owned(scalar_name, Sort::Int);
    assert_ne!(length(&func, 1), scalar_value);
    func.postconditions = vec![result_eq(length(&func, 1))];
    ay(&pinned_post(&func, 1), true);
    func.postconditions = vec![result_eq(scalar_value)];
    ay(&pinned_post(&func, 1), false);
}

#[test]
fn projected_metadata_source_is_not_a_whole_stable_parameter() {
    let mut func = subject(reference(slice(), false), false, false);
    func.body.locals[1].ty = Ty::Tuple(vec![reference(slice(), false)]);
    func.body.blocks[0].stmts[0] = assign(
        0,
        Rvalue::UnaryOp(
            UnOp::PtrMetadata,
            Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] }),
        ),
    );
    func.postconditions =
        vec![Formula::Ge(Box::new(Formula::var("_0", Sort::Int)), Box::new(Formula::Int(0)))];
    refused(&func);
}

#[test]
fn malformed_metadata_source_destination_and_local_identity_are_rejected() {
    let original = subject(reference(slice(), false), false, false);
    let mut wrong_source = original.clone();
    wrong_source.body.locals[1].ty = Ty::usize();
    assert!(crate::try_generate_vcs(&wrong_source).is_err());
    for dest in
        [Ty::Bool, Ty::Int { width: 32, signed: false }, Ty::Int { width: 64, signed: true }]
    {
        let mut wrong_dest = original.clone();
        wrong_dest.body.locals[0].ty = dest.clone();
        wrong_dest.body.return_ty = dest;
        assert!(crate::try_generate_vcs(&wrong_dest).is_err());
    }
    let mut wrong_identity = original;
    wrong_identity.body.locals[1].index = 2;
    assert!(crate::try_generate_vcs(&wrong_identity).is_err());
}

#[test]
fn thin_unit_and_dynamic_metadata_cannot_become_slice_length_returns() {
    for pointer in [
        reference(Ty::Array { elem: Box::new(Ty::Int { width: 8, signed: false }), len: 7 }, false),
        raw(Ty::usize(), false),
        reference(
            Ty::Dynamic {
                trait_name: "test::Trait".into(),
                principal_key: Some("test::Trait".into()),
            },
            false,
        ),
    ] {
        let mut func = subject(reference(slice(), false), false, false);
        func.body.locals[1].ty = pointer;
        assert_eq!(
            crate::ptr_metadata_model(&func, &Operand::Copy(Place::local(1))),
            crate::PtrMetadataModel::Unsupported
        );
        refused(&func);
    }
    let mut unit = subject(reference(slice(), false), false, false);
    unit.body.locals[1].ty = raw(Ty::usize(), false);
    unit.body.locals[0].ty = Ty::Unit;
    unit.body.return_ty = Ty::Unit;
    unit.postconditions.clear();
    crate::validate_function(&unit).unwrap();
    assert_eq!(
        crate::ptr_metadata_model(&unit, &Operand::Copy(Place::local(1))),
        crate::PtrMetadataModel::Unit
    );
    assert!(crate::chc::rvalue_to_formula(&unit, &metadata(1, false)).is_err());
}

#[test]
fn multiple_return_writes_cannot_supply_stale_or_contradictory_metadata_pins() {
    for predecessor in [false, true] {
        for after in [false, true] {
            for other_metadata in [false, true] {
                let mut func = subject(reference(slice(), false), false, predecessor);
                let competing = if other_metadata {
                    metadata(2, false)
                } else {
                    Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64)))
                };
                if predecessor && after {
                    func.body.blocks[1].stmts.push(assign(0, competing));
                } else {
                    func.body.blocks[0].stmts.insert(usize::from(after), assign(0, competing));
                }
                refused(&func);
            }
        }
    }
}

#[test]
fn post_write_calls_and_opaque_effects_leave_visible_metadata_obligations() {
    let mut called = subject(reference(slice(), false), false, true);
    let unit = append_local(&mut called, Ty::Unit);
    called.body.blocks[0].terminator = call(unit, 1, vec![]);
    refused(&called);

    let mut overwritten = subject(reference(slice(), false), false, true);
    overwritten.body.blocks[0].terminator = call(0, 1, vec![]);
    refused(&overwritten);

    let mut opaque_stmt = subject(reference(slice(), false), false, false);
    opaque_stmt.body.blocks[0].stmts.push(Statement::Unsupported {
        kind: "test::opaque_effect".into(),
        detail: "no modeled write footprint".into(),
        operands: vec![],
        span: SourceSpan::default(),
    });
    refused(&opaque_stmt);

    let mut opaque_edge = subject(reference(slice(), false), false, true);
    opaque_edge.body.blocks[0].terminator = Terminator::Opaque {
        kind: "test::opaque_control".into(),
        targets: vec![BlockId(1)],
        span: SourceSpan::default(),
    };
    refused(&opaque_edge);
}

#[test]
fn metadata_definition_beyond_the_return_pair_keeps_a_visible_obligation() {
    for post_write_call in [false, true] {
        let mut func = subject(reference(slice(), false), false, true);
        // The selected predecessor/Return pair is now bb1/bb2. The live
        // metadata definition in bb0 cannot be treated as NotApplicable merely
        // because positive pin admission only covers two adjacent blocks.
        func.body.blocks[1].terminator = Terminator::Goto(BlockId(2));
        func.body.blocks.push(BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        if post_write_call {
            let unit = append_local(&mut func, Ty::Unit);
            func.body.blocks[0].terminator = call(unit, 1, vec![]);
        }
        refused(&func);
    }
}

#[test]
fn pointee_effect_epochs_preserve_ay_discrimination_and_distinct_slice_identity() {
    // ADDITIVE subject control, not part of the original 19-test baseline.
    // Each body keeps xs.len() == 1 and ys.len() == 2. The unchanged body
    // must prove result == xs.len(), refute its negation, and refute a claim
    // about the distinct second slice. A contradictory epoch normalization
    // would wrongly prove one of the false clauses.
    for predecessor in [false, true] {
        for after in [false, true] {
            for effect in 0..4 {
                let mut func = subject(reference(slice(), true), false, predecessor);
                let xs_len = length(&func, 1);
                let ys_len = length(&func, 2);
                assert_ne!(xs_len, ys_len);
                func.preconditions = vec![
                    Formula::Eq(Box::new(xs_len.clone()), Box::new(Formula::Int(1))),
                    Formula::Eq(Box::new(ys_len.clone()), Box::new(Formula::Int(2))),
                ];
                let pointee = Place { local: 1, projections: vec![Projection::Deref] };
                let statement = if effect == 0 {
                    Statement::Assign {
                        place: Place {
                            local: 1,
                            projections: vec![
                                Projection::Deref,
                                Projection::ConstantIndex {
                                    offset: 0,
                                    min_length: 1,
                                    from_end: false,
                                },
                            ],
                        },
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))),
                        span: SourceSpan::default(),
                    }
                } else {
                    let alias_ty = if effect == 1 {
                        reference(slice(), true)
                    } else {
                        raw(slice(), effect == 3)
                    };
                    let dest = append_local(&mut func, alias_ty);
                    let borrow = if effect == 1 {
                        Rvalue::Ref { mutable: true, place: pointee }
                    } else {
                        Rvalue::AddressOf(effect == 3, pointee)
                    };
                    assign(dest, borrow)
                };
                if predecessor && after {
                    // Metadata read in the predecessor, effect in the Return
                    // block: the two observation points still see one length.
                    func.body.blocks[1].stmts.push(statement);
                } else {
                    func.body.blocks[0].stmts.insert(usize::from(after), statement);
                }
                func.postconditions = vec![result_eq(xs_len.clone())];
                ay(&pinned_post(&func, 1), true);
                func.postconditions = vec![Formula::Not(Box::new(result_eq(xs_len)))];
                ay(&pinned_post(&func, 1), false);
                func.postconditions = vec![result_eq(ys_len.clone())];
                let wrong_slice = pinned_post(&func, 1);
                assert!(!spine_pins_value(&wrong_slice.formula, &ys_len), "{wrong_slice:?}");
                ay(&wrong_slice, false);
            }
        }
    }
}

#[test]
fn stable_length_epoch_normalization_is_exact_typed_and_capture_avoiding() {
    use super::return_metadata::{MetadataReturnPin, normalize_stable_length_epochs};

    let canonical = Formula::var("xs__slice_len", Sort::Int);
    let pin = MetadataReturnPin::Exact(canonical.clone());
    let epoch = Formula::var("xs__slice_len#s0_pre", Sort::Int);
    let interned_epoch = Formula::SymVar("xs__slice_len#s2_t".into(), Sort::Int);
    let input = Formula::Eq(Box::new(epoch.clone()), Box::new(interned_epoch.clone()));
    assert_eq!(
        normalize_stable_length_epochs(input.clone(), &pin),
        Formula::Eq(Box::new(canonical.clone()), Box::new(canonical.clone()))
    );

    for unchanged in [
        canonical.clone(),
        Formula::var("ys__slice_len#s0_pre", Sort::Int),
        Formula::SymVar("ys__slice_len#s2_t".into(), Sort::Int),
        Formula::var("xs#s0_pre", Sort::Int),
        Formula::var("xs*.0__slice_len#s0_pre", Sort::Int),
        Formula::var("xs__slice_len_more#s0_pre", Sort::Int),
        Formula::var("xs__slice_len#s0_pre.0", Sort::Int),
        Formula::var("xs__slice_len#s0_pre", Sort::Bool),
        Formula::SymVar("xs__slice_len#s2_t".into(), Sort::Bool),
        Formula::var("xs__slice_len#", Sort::Int),
        Formula::var("xs__slice_len##s0_pre", Sort::Int),
        Formula::var("xs__slice_len#s0-pre", Sort::Int),
        Formula::var("xs__slice_len#sö", Sort::Int),
    ] {
        assert_eq!(normalize_stable_length_epochs(unchanged.clone(), &pin), unchanged);
    }

    for exists in [false, true] {
        let bound_epoch_body = Formula::Eq(
            Box::new(epoch.clone()),
            Box::new(Formula::SymVar("xs__slice_len#s0_pre".into(), Sort::Int)),
        );
        let bound_epoch = if exists {
            Formula::Exists(
                vec![("xs__slice_len#s0_pre".into(), Sort::Int)],
                Box::new(bound_epoch_body),
            )
        } else {
            Formula::Forall(
                vec![("xs__slice_len#s0_pre".into(), Sort::Int)],
                Box::new(bound_epoch_body),
            )
        };
        assert_eq!(normalize_stable_length_epochs(bound_epoch.clone(), &pin), bound_epoch);

        // Renaming this free epoch to the canonical name inside the quantifier
        // would capture it. The entire target-shadowing subtree stays intact.
        let shadowed_body =
            Formula::Eq(Box::new(interned_epoch.clone()), Box::new(canonical.clone()));
        let target_shadowed = if exists {
            Formula::Exists(vec![("xs__slice_len".into(), Sort::Int)], Box::new(shadowed_body))
        } else {
            Formula::Forall(vec![("xs__slice_len".into(), Sort::Int)], Box::new(shadowed_body))
        };
        assert_eq!(normalize_stable_length_epochs(target_shadowed.clone(), &pin), target_shadowed);
    }

    for declined in [MetadataReturnPin::NotApplicable, MetadataReturnPin::Unsupported("test gap")] {
        assert_eq!(normalize_stable_length_epochs(input.clone(), &declined), input);
    }
}

#[test]
fn generic_chc_metadata_refusal_is_unchanged_even_for_supported_return_shape() {
    let func = subject(reference(slice(), false), false, false);
    assert!(matches!(
        crate::ptr_metadata_model(&func, &Operand::Copy(Place::local(1))),
        crate::PtrMetadataModel::Length(_)
    ));
    assert!(crate::chc::rvalue_to_formula(&func, &metadata(1, false)).is_err());
}

#[test]
#[ignore = "requires TRUST_RETURN_METADATA_A9_INPUT pointing to the retained, externally hash-bound A9 extraction"]
fn retained_a9_window_end_preserves_each_return_pin_and_wrong_clause_control() {
    let path = std::env::var_os("TRUST_RETURN_METADATA_A9_INPUT")
        .expect("set TRUST_RETURN_METADATA_A9_INPUT to the retained window_end MIR JSON");
    let info = std::fs::metadata(&path).unwrap();
    assert!(info.is_file() && info.len() <= 4 * 1024 * 1024);
    let bytes = std::fs::read(&path).unwrap();
    let original: VerifiableFunction = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(original.def_path, "a9_bounds_safety::window_end");
    assert_eq!(original.name, "window_end");
    assert_eq!(original.body.locals.len(), 9);
    assert_eq!(original.body.blocks.len(), 6);
    assert_eq!(original.body.arg_count, 3);
    assert_eq!(original.contracts.len(), 2);
    assert_eq!(original.preconditions.len(), 3);
    assert_eq!(original.postconditions.len(), 1);
    assert_eq!(
        original
            .body
            .blocks
            .iter()
            .filter(|bb| matches!(bb.terminator, Terminator::Assert { .. }))
            .count(),
        2
    );
    assert_eq!(
        original
            .body
            .blocks
            .iter()
            .filter(|bb| matches!(bb.terminator, Terminator::Return))
            .count(),
        1
    );
    assert_eq!(original.body.blocks.iter().flat_map(|bb| &bb.stmts).filter(|stmt|
        matches!(stmt, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty())).count(), 2);
    assert!(matches!(&original.body.blocks[2].stmts[0], Statement::Assign {
        place, rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(source)), ..
    } if place.local == 0 && place.projections.is_empty() && source.local == 1 && source.projections.is_empty()));
    let expected_post = Formula::Ge(
        Box::new(Formula::var("_0", Sort::Int)),
        Box::new(Formula::var("start", Sort::Int)),
    );
    assert_eq!(original.postconditions, vec![expected_post]);

    for false_clause in [false, true] {
        let mut func = original.clone();
        if false_clause {
            func.postconditions = vec![Formula::Lt(
                Box::new(Formula::var("_0", Sort::Int)),
                Box::new(Formula::var("start", Sort::Int)),
            )];
            let clause = "(result) < (start)";
            func.spec.ensures = vec![clause.into()];
            for contract in &mut func.contracts {
                if matches!(contract.kind, ContractKind::Ensures) {
                    contract.body =
                        format!("{}{clause}", crate::contracts::LOWERED_CONTRACT_PREFIX);
                }
            }
        }
        let vcs = emit(&func);
        let posts: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
        assert_eq!(posts.len(), 2, "one postcondition per actual return predecessor: {vcs:?}");
        assert!(posts.iter().all(|vc| formula_has_return_slot_pin(&vc.formula)), "{posts:?}");
        assert!(
            !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == "SpecUnverifiable")),
            "{vcs:?}"
        );
        let metadata_posts: Vec<_> =
            posts.iter().filter(|vc| spine_pins_value(&vc.formula, &length(&func, 1))).collect();
        assert_eq!(
            metadata_posts.len(),
            1,
            "the metadata edge must be pinned to xs, not the arithmetic edge: {posts:?}"
        );
        // This is the exact metadata-return arm of the retained MIR, not a
        // replacement synthetic function or a modified VC kind/formula.
        ay(metadata_posts[0], !false_clause);
    }
    assert_eq!(std::fs::read(&path).unwrap(), bytes, "the retained producer input is read-only");
}
