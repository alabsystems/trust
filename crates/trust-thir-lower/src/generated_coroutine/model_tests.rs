use trust_ir::{FieldDef, StructRepr};

use super::*;

fn projection(types: Vec<Ty>, selected: usize) -> ScalarBody {
    ScalarBody {
        name: "generated::scalar".into(),
        types: vec![],
        predicates: vec![],
        structs: vec![StructDef {
            id: StructId::new(0),
            name: "generated::frame".into(),
            fields: types
                .iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("__upvar{i}"),
                    ty: ty.clone(),
                    offset: None,
                })
                .collect(),
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        }],
        locals: vec![types[selected].clone(), Ty::Struct(StructId::new(0)), Ty::Unit],
        blocks: vec![ScalarBlock {
            statements: vec![Statement::Assign {
                destination: 0,
                operand: Operand::Capture {
                    field: selected,
                    ty: types[selected].clone(),
                    moved: false,
                },
            }],
            terminator: Terminator::Return,
        }],
    }
}

#[test]
fn every_scalar_capture_position_has_real_ssa_and_no_authority() {
    for ty in [
        Ty::Bool,
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::Isize,
        Ty::Usize,
    ] {
        for selected in 0..3 {
            let body = projection(vec![ty.clone(); 3], selected);
            let module = lower(&body).unwrap();
            assert!(trust_ir_build::validate_module(&module).is_empty());
            let function = &module.functions[0];
            assert_eq!(function.blocks[0].body.len(), 2);
            assert!(matches!(&function.blocks[0].body[0].inst,
                Inst::ExtractField { field, ty: actual, .. } if *field == selected as u32 && *actual == ty));
            assert_eq!(function.producer, Some(Producer::Other(PRODUCER.into())));
            assert!(function.proofs.is_empty() && function.summary.is_none());
            assert!(function.source_provenance.is_none());
            assert!(
                function.blocks[0].body.iter().all(|node| !matches!(node.inst, Inst::Undef { .. }))
            );
        }
    }
}

#[test]
fn changing_selected_capture_changes_the_actual_function() {
    let first = lower(&projection(vec![Ty::U32; 2], 0)).unwrap();
    let second = lower(&projection(vec![Ty::U32; 2], 1)).unwrap();
    assert_ne!(first.stable_digest(), second.stable_digest());
    assert_ne!(first.functions[0], second.functions[0]);
}

#[test]
fn interpreter_observes_the_actual_selected_capture_not_a_placeholder() {
    use trust_ir::{InterpretValue, InterpretValueKind, Interpreter};
    for selected in 0..2 {
        let module = lower(&projection(vec![Ty::U32; 2], selected)).unwrap();
        for values in [[0, 1], [17, 99], [u32::MAX as i128, 0]] {
            let captures = values.map(|value| InterpretValue::int(Ty::U32, value).unwrap());
            let actual = Interpreter::with_module(&module)
                .execute_function(
                    &module.functions[0],
                    [
                        InterpretValue {
                            ty: Ty::Struct(StructId::new(0)),
                            kind: InterpretValueKind::Aggregate(captures.to_vec()),
                        },
                        InterpretValue { ty: Ty::Unit, kind: InterpretValueKind::Unit },
                    ],
                )
                .unwrap();
            assert_eq!(actual.returns, vec![captures[selected].clone()]);
        }
    }
}

#[test]
fn rejects_wrong_capture_width_sign_index_or_return_type() {
    for replacement in [Ty::I32, Ty::U16, Ty::U64, Ty::Unit] {
        let mut body = projection(vec![Ty::U32; 2], 0);
        let Statement::Assign { operand: Operand::Capture { ty, .. }, .. } =
            &mut body.blocks[0].statements[0]
        else {
            unreachable!()
        };
        *ty = replacement;
        assert!(lower(&body).is_err());
    }
    let mut body = projection(vec![Ty::U32; 2], 0);
    body.locals[0] = Ty::I32;
    assert!(lower(&body).is_err());
    let Statement::Assign { operand: Operand::Capture { field, .. }, .. } =
        &mut body.blocks[0].statements[0]
    else {
        unreachable!()
    };
    *field = 2;
    assert!(lower(&body).is_err());
}

#[test]
fn scalar_copy_chains_and_storage_are_checked() {
    let mut body = projection(vec![Ty::U32], 0);
    body.locals.push(Ty::U32);
    body.blocks[0].statements = vec![
        Statement::StorageLive(3),
        Statement::Assign {
            destination: 3,
            operand: Operand::Capture { field: 0, ty: Ty::U32, moved: true },
        },
        Statement::Assign { destination: 0, operand: Operand::Local { local: 3, moved: true } },
        Statement::StorageDead(3),
    ];
    assert!(lower(&body).is_ok());
    body.blocks[0].statements.swap(2, 3);
    assert!(lower(&body).is_err());
    body.blocks[0].statements = vec![
        Statement::StorageLive(3),
        Statement::StorageDead(3),
        Statement::Assign {
            destination: 3,
            operand: Operand::Capture { field: 0, ty: Ty::U32, moved: false },
        },
        Statement::Assign { destination: 0, operand: Operand::Local { local: 3, moved: false } },
    ];
    assert!(lower(&body).is_err(), "writing dead storage must not resurrect its lifetime");
}

#[test]
fn rejects_second_capture_move_and_uninitialized_return() {
    let mut body = projection(vec![Ty::U32], 0);
    let first = Statement::Assign {
        destination: 0,
        operand: Operand::Capture { field: 0, ty: Ty::U32, moved: true },
    };
    body.blocks[0].statements = vec![first.clone(), first];
    assert!(lower(&body).is_err());
    body.blocks[0].statements.clear();
    assert!(lower(&body).is_err());
}

#[test]
fn no_unknown_slot_or_whole_resume_frame_read_is_erased() {
    for local in [1, 2, 99] {
        let mut body = projection(vec![Ty::U32], 0);
        body.blocks[0].statements[0] =
            Statement::Assign { destination: 0, operand: Operand::Local { local, moved: false } };
        assert!(lower(&body).is_err());
        body.blocks[0].statements[0] = Statement::StorageDead(local);
        assert!(lower(&body).is_err());
    }
}

#[test]
fn all_blocks_are_required_and_goto_cycles_fail_closed() {
    let mut body = projection(vec![Ty::U32], 0);
    body.blocks
        .push(ScalarBlock { statements: vec![Statement::Nop], terminator: Terminator::Return });
    assert!(lower(&body).is_err());
    body.blocks[0].terminator = Terminator::Goto(1);
    assert!(lower(&body).is_ok());
    body.blocks[1].terminator = Terminator::Goto(0);
    assert!(lower(&body).is_err());
    body.blocks[1].terminator = Terminator::Goto(9);
    assert!(lower(&body).is_err());
}

#[test]
fn exact_scalar_constants_have_real_instructions() {
    let mut body = projection(vec![Ty::U8], 0);
    for value in [0, 1, 255] {
        body.blocks[0].statements[0] = Statement::Assign {
            destination: 0,
            operand: Operand::Constant { ty: Ty::U8, value: Constant::Int(value) },
        };
        assert!(lower(&body).is_ok());
    }
    for value in [-1, 256] {
        body.blocks[0].statements[0] = Statement::Assign {
            destination: 0,
            operand: Operand::Constant { ty: Ty::U8, value: Constant::Int(value) },
        };
        assert!(lower(&body).is_err());
    }
}

#[test]
fn concrete_unused_resume_fields_are_retained_not_unit() {
    let mut body = resume_projection(false);
    let module = lower(&body).unwrap();
    assert_eq!(module.structs, body.structs);
    assert_eq!(module.func_types[0].params[1], body.locals[2]);
    body.structs[1].fields.clear();
    assert!(lower(&body).is_err());
}

fn resume_projection(nonnull: bool) -> ScalarBody {
    let mut body = projection(vec![Ty::U32], 0);
    let pointer = if nonnull {
        let mut table = Module::new("test-resume-tables");
        let base = table.add_type(Ty::Ptr).expect("Module::add_type: test fixture");
        let predicate =
            table.intern_pred(Pred::NonNull).expect("Module::intern_pred: test fixture").unwrap();
        body.types = table.types;
        body.predicates = table.predicates;
        Ty::Refine(base, predicate)
    } else {
        Ty::Ptr
    };
    body.structs.push(StructDef {
        id: StructId::new(1),
        name: "resume::NonNull".into(),
        fields: vec![FieldDef { name: "pointer".into(), ty: pointer, offset: Some(0) }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Transparent,
        origin: None,
    });
    body.structs.push(StructDef {
        id: StructId::new(2),
        name: "resume::ResumeTy".into(),
        fields: vec![FieldDef {
            name: "0".into(),
            ty: Ty::Struct(StructId::new(1)),
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    body.locals[2] = Ty::Struct(StructId::new(2));
    body
}

#[test]
fn nonnull_resume_retains_exact_refinement_tables_and_computational_ssa() {
    let body = resume_projection(true);
    let module = lower(&body).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(module.structs, body.structs);
    assert_eq!(module.types, [Ty::Ptr]);
    assert_eq!(module.predicates, [Pred::NonNull]);
    assert_eq!(module.structs[1].fields[0].ty, Ty::Refine(TyId::new(0), PredId::new(0)));
    let raw = lower(&resume_projection(false)).unwrap();
    assert_eq!(
        module.functions, raw.functions,
        "unused resume restriction does not change scalar computation"
    );
    assert_ne!(
        module.stable_digest(),
        raw.stable_digest(),
        "the restriction itself remains semantic content"
    );
    let function = &module.functions[0];
    assert!(
        function.proofs.is_empty()
            && function.summary.is_none()
            && function.source_provenance.is_none()
    );
    assert!(module.proof_obligations.is_empty() && module.proof_certificates.is_empty());
    assert_eq!(function.producer, Some(Producer::Other(PRODUCER.into())));
}

#[test]
fn nonnull_resume_rejects_invalid_predicates_bases_and_table_shape() {
    for predicate in
        [Pred::Top, Pred::Bottom, Pred::NonZero, Pred::Conj(vec![]), Pred::Disj(vec![])]
    {
        let mut body = resume_projection(true);
        body.predicates[0] = predicate;
        assert!(lower(&body).is_err());
    }
    for base in [
        Ty::U64,
        Ty::Unit,
        Ty::FatPtr(trust_ir::FatPtrKind::Str),
        Ty::Refine(TyId::new(0), PredId::new(0)),
    ] {
        let mut body = resume_projection(true);
        body.types[0] = base;
        assert!(lower(&body).is_err());
    }
    for table in 0..4 {
        let mut body = resume_projection(true);
        match table {
            0 => body.types.clear(),
            1 => body.predicates.clear(),
            2 => body.types.push(Ty::Ptr),
            _ => body.predicates.push(Pred::NonNull),
        }
        assert!(lower(&body).is_err());
    }
}

#[test]
fn nonnull_resume_rejects_dangling_erased_or_unused_refinements() {
    for ty in [
        Ty::Refine(TyId::new(1), PredId::new(0)),
        Ty::Refine(TyId::new(0), PredId::new(1)),
        Ty::Refine(TyId::new(u32::MAX), PredId::new(u32::MAX)),
        Ty::Ptr,
        Ty::FatPtr(trust_ir::FatPtrKind::Str),
        Ty::Unit,
    ] {
        let mut body = resume_projection(true);
        body.structs[1].fields[0].ty = ty;
        assert!(lower(&body).is_err(), "invalid or erased source restriction");
    }
    let mut body = resume_projection(true);
    body.structs.truncate(1);
    body.locals[2] = Ty::Unit;
    assert!(lower(&body).is_err(), "unused authority-shaped tables are not retained");
    let mut body = resume_projection(true);
    body.locals[2] = Ty::Struct(StructId::new(1));
    assert!(lower(&body).is_err(), "outer wrapper cannot silently disappear");
}

#[test]
fn nonnull_resume_rejects_wrong_wrapper_layouts_and_disconnected_types() {
    for index in [1, 2] {
        for mutation in 0..9 {
            let mut body = resume_projection(true);
            let wrapper = &mut body.structs[index];
            match mutation {
                0 => wrapper.fields[0].offset = Some(1),
                1 => wrapper.fields[0].offset = None,
                2 => wrapper.size = Some(16),
                3 => wrapper.size = None,
                4 => wrapper.align = Some(4),
                5 => wrapper.align = Some(3),
                6 => wrapper.align = None,
                7 => wrapper.fields.push(wrapper.fields[0].clone()),
                _ => wrapper.id = StructId::new(9),
            }
            assert!(lower(&body).is_err(), "wrapper {index}, mutation {mutation}");
        }
    }
    let mut body = resume_projection(true);
    body.structs[2].fields[0].ty = Ty::Struct(StructId::new(0));
    assert!(lower(&body).is_err());
    body.structs[2].fields[0].ty = Ty::Struct(StructId::new(2));
    assert!(lower(&body).is_err());
}

#[test]
fn exact_resume_layout_requires_thin_64bit_pointer_and_exact_validity_range() {
    let full = (0, u64::MAX as u128);
    let nonnull = (1, u64::MAX as u128);
    assert!(exact_resume_pointer_layout(8, (8, 8), (8, 8), full, nonnull, true));
    assert!(exact_resume_pointer_layout(8, (8, 8), (8, 8), full, full, false));
    for target in [0, 4, 16, u64::MAX] {
        assert!(!exact_resume_pointer_layout(target, (8, 8), (8, 8), full, nonnull, true));
    }
    for layout in [(0, 8), (4, 4), (16, 8), (8, 4), (8, 16), (8, 3), (u64::MAX, 8)] {
        assert!(!exact_resume_pointer_layout(8, layout, (8, 8), full, nonnull, true));
        assert!(!exact_resume_pointer_layout(8, (8, 8), layout, full, nonnull, true));
    }
    for range in [full, (1, 1), (2, u64::MAX as u128), (1, u128::MAX), (1, 0)] {
        assert!(!exact_resume_pointer_layout(8, (8, 8), (8, 8), full, range, true));
    }
    assert!(!exact_resume_pointer_layout(8, (8, 8), (8, 8), nonnull, nonnull, true));
    assert!(!exact_resume_pointer_layout(8, (8, 8), (8, 8), full, nonnull, false));
}

#[test]
fn nonnull_resume_stays_unusable_as_a_runtime_operand_or_destination() {
    for moved in [false, true] {
        let mut body = resume_projection(true);
        body.blocks[0].statements[0] =
            Statement::Assign { destination: 0, operand: Operand::Local { local: 2, moved } };
        assert!(lower(&body).is_err());
    }
    for statement in [
        Statement::StorageLive(2),
        Statement::StorageDead(2),
        Statement::Assign {
            destination: 2,
            operand: Operand::Constant { ty: Ty::Unit, value: Constant::PhantomData },
        },
    ] {
        let mut body = resume_projection(true);
        body.blocks[0].statements.insert(0, statement);
        assert!(lower(&body).is_err());
    }
    let mut body = resume_projection(true);
    body.locals[0] = body.locals[2].clone();
    assert!(lower(&body).is_err());
    body.locals[0] = Ty::U32;
    body.locals.push(Ty::Refine(TyId::new(0), PredId::new(0)));
    assert!(lower(&body).is_err(), "no refinement-valued temporary enters the scalar slice");
}

#[test]
fn nonnull_resume_metadata_and_predicate_mutations_change_the_exact_artifact() {
    let body = resume_projection(true);
    let module = lower(&body).unwrap();
    let digest = module.stable_digest();
    let mut changed = module.clone();
    changed.predicates[0] = Pred::Top;
    assert_ne!(digest, changed.stable_digest());
    let mut changed = module.clone();
    changed.structs[1].fields[0].ty = Ty::Ptr;
    assert_ne!(digest, changed.stable_digest());
    for index in [1, 2] {
        let mut changed = body.clone();
        changed.structs[index].name.push_str("::different-source-type");
        assert_ne!(digest, lower(&changed).unwrap().stable_digest());
        let mut changed = body.clone();
        changed.structs[index].fields[0].name.push_str("::different-field");
        assert_ne!(digest, lower(&changed).unwrap().stable_digest());
    }
    let mut changed = module.clone();
    changed.functions[0].producer = Some(Producer::Other("forged-authority-label".into()));
    assert_ne!(digest, changed.stable_digest());
    // A cloned/changed module is not the sealed retained outcome and has no
    // conversion to an executable capability; no digest test grants one.
    assert_eq!(module, lower(&body).unwrap());
}

#[test]
fn source_name_or_capture_carrier_changes_invalidate_old_digest() {
    let mut body = projection(vec![Ty::U32], 0);
    let original = lower(&body).unwrap().stable_digest();
    body.name.push_str("::changed");
    assert_ne!(original, lower(&body).unwrap().stable_digest());
    let wider = lower(&projection(vec![Ty::U64], 0)).unwrap().stable_digest();
    assert_ne!(original, wider);
}

#[test]
fn bounded_input_limits_are_real_refusals() {
    let mut body = projection(vec![Ty::U32], 0);
    body.locals.resize(4097, Ty::U32);
    assert!(lower(&body).is_err());
    let mut body = projection(vec![Ty::U32], 0);
    body.blocks[0].statements.resize(4097, Statement::Nop);
    assert!(lower(&body).is_err());
    let body = projection(vec![Ty::U32; 65], 0);
    assert!(lower(&body).is_err());
}
