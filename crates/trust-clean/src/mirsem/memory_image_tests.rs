//! Synthetic carrier refusal controls, not compiler extraction or an allocation
//! model. Scalar/whole-function certificates must not confer semantics on images.

use trust_types::{
    BasicBlock, BinOp, BlockId, CallableDefPathHash, ConstValue, ConstantImageLayout,
    ConstantImageOwner, ConstantImageRoot, ConstantImageTarget, ConstantMemoryImage, LocalDecl,
    Operand, Place, Rvalue, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::*;

fn image() -> ConstValue {
    ConstValue::MemoryImage(Box::new(ConstantMemoryImage {
        schema_version: 1,
        owner: ConstantImageOwner {
            def_path: "fixture".into(),
            def_path_hash: CallableDefPathHash::new(1, 2),
            mir_phase: "test".into(),
        },
        target: ConstantImageTarget {
            triple: "test".into(),
            data_layout: "e-p:64:64".into(),
            pointer_size_bytes: 8,
            little_endian: true,
        },
        ty: Ty::u8(),
        ty_fingerprint: [1, 2],
        layout: ConstantImageLayout { size_bytes: 1, align_bytes: 1 },
        root: ConstantImageRoot::ScalarBits { bits: 7, size_bytes: 1 },
        nodes: Default::default(),
    }))
}

fn nested_image() -> ConstValue {
    ConstValue::struct_scalar_fields_ref(
        "Outer",
        vec![ConstValue::struct_scalar_fields_ref("Inner", vec![image()])],
    )
}

fn scalar_add() -> VerifiableFunction {
    VerifiableFunction {
        name: "scalar_add".into(),
        def_path: "fixture::scalar_add".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: (0..4).map(|index| LocalDecl { index, ty: Ty::u32(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn assert_body_certificates_refuse(func: &VerifiableFunction) {
    assert!(function_adequacy_witness(func).is_none());
    assert!(whole_function_refinement_witness(func).is_none());
    assert!(function_fully_faithful_witness(func).is_none());
    assert!(function_safety_vcs_faithful(func).is_none());
    assert!(function_safety_vc_faithful(func).is_none());
    assert!(function_emits_declined_vc(func));
    assert!(function_has_open_declined_vc(func));
    assert!(!crate::trustir_safety::function_safety_vcs_faithful_via_trustir(func));
}

#[test]
fn memory_image_scalar_operand_and_rvalue_whitelists_refuse_direct_and_nested() {
    let func = scalar_add();
    let param = |local: usize| {
        if (1..=2).contains(&local) { Some((local - 1) as u64) } else { None }
    };
    assert_eq!(
        sem_operand_of_mir(&func.body, &Operand::Constant(ConstValue::Int(7)), &param),
        Some(SemOperand::Const(7)),
    );
    for value in [image(), nested_image()] {
        let operand = Operand::Constant(value);
        assert!(sem_operand_of_mir(&func.body, &operand, &param).is_none());
        for rvalue in [
            Rvalue::Use(operand.clone()),
            Rvalue::BinaryOp(BinOp::Add, operand.clone(), Operand::Constant(ConstValue::Int(0))),
            Rvalue::BinaryOp(BinOp::Eq, operand.clone(), operand.clone()),
        ] {
            assert!(sem_rvalue_of_mir(&func.body, &rvalue, &param).is_none(), "{rvalue:?}");
        }
    }
}

#[test]
fn memory_image_direct_and_nested_add_cannot_mint_width_only_certificates() {
    for value in [image(), nested_image()] {
        let mut func = scalar_add();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, lhs, _), .. } =
            &mut func.body.blocks[0].stmts[0]
        else {
            panic!("scalar-add fixture");
        };
        *lhs = Operand::Constant(value);
        // Width recognition alone deliberately cannot authorize this body.
        assert_eq!(function_uadd_overflow_widths(&func), vec![UWidth::W32]);
        assert_body_certificates_refuse(&func);
    }
}

#[test]
fn memory_image_dead_assignment_and_dead_block_refuse_function_certificates() {
    for value in [image(), nested_image()] {
        let statement = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Constant(value)),
            span: Default::default(),
        };
        let mut unused = scalar_add();
        unused.body.blocks[0].stmts.insert(0, statement.clone());
        assert_body_certificates_refuse(&unused);
        let mut unreachable = scalar_add();
        unreachable.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![statement],
            terminator: Terminator::Return,
        });
        assert_body_certificates_refuse(&unreachable);
    }
}

#[test]
fn memory_image_refusal_preserves_plain_scalar_width_certificate() {
    let certs = function_safety_vc_faithful(&scalar_add())
        .expect("existing unsigned-add width hook remains admitted");
    assert_eq!(certs.len(), 1);
    assert_eq!(certs[0].width, UWidth::W32);
    assert!(certs[0].is_modulo_3());
}
