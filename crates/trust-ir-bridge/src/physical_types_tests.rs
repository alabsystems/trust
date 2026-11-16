//! Synthetic bridge integration regressions, not captured Clean-helper bodies.
//!
//! These exercise the real body-table consumer and interpreter. Their authored
//! layouts establish test inputs, not Rust-source correspondence or proof grade.

use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty as IrTy;
use trust_ir::{Function, Module, ProofAnnotation};
use trust_ir_build::validate_module;
use trust_types::{
    AdtKind, AdtLayoutInfo, AggregateKind, BasicBlock, BlockId, ConstValue, DatatypeDefs,
    LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

use crate::lower::{lower_to_trust_ir, lower_to_trust_ir_functions};

const VALUE: &str = "synthetic_physical::Value";

fn marker() -> Ty {
    Ty::Datatype { name: VALUE.into(), variants: vec![] }
}

fn structure(name: &str, fields: Vec<Ty>) -> Ty {
    let count = fields.len();
    Ty::Adt {
        name: name.into(),
        fields: fields.into_iter().enumerate().map(|(i, ty)| (i.to_string(), ty)).collect(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: Some(Box::new(AdtLayoutInfo {
            size: count as u64 * 8,
            align: 8,
            field_offsets: (0..count as u64).map(|i| i * 8).collect(),
            repr: "c".into(),
        })),
        enum_layout: None,
        adt_kind: Some(AdtKind::Struct),
    }
}

fn definitions(fields: Vec<Ty>) -> DatatypeDefs {
    [(VALUE.into(), structure(VALUE, fields))].into()
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn field(local: usize, indices: &[usize]) -> Place {
    Place { local, projections: indices.iter().map(|i| Projection::Field(*i)).collect() }
}

fn reader(
    name: &str,
    argument: Ty,
    result: Ty,
    indices: &[usize],
    datatype_defs: DatatypeDefs,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("synthetic_physical::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: result.clone(), name: None },
                LocalDecl { index: 1, ty: argument, name: Some("input".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(field(1, indices))))],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: result,
            datatype_defs,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn valid(module: &Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "invalid synthetic bridge output: {errors:?}");
}

fn instructions(function: &Function) -> impl Iterator<Item = &Inst> {
    function.blocks.iter().flat_map(|block| block.body.iter()).map(|node| &node.inst)
}

fn argument_type(function: &Function) -> IrTy {
    let entry = function.blocks.iter().find(|block| block.id == function.entry).expect("entry");
    assert_eq!(entry.params.len(), 1);
    entry.params[0].1.clone()
}

fn aggregate(ty: IrTy, fields: Vec<InterpretValue>) -> InterpretValue {
    InterpretValue { ty, kind: InterpretValueKind::Aggregate(fields) }
}

fn integer(ty: IrTy, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("fixture integer fits")
}

fn returns(module: &Module, index: usize, args: Vec<InterpretValue>, expected: InterpretValue) {
    let outcome = Interpreter::with_module(module)
        .execute_func(module.functions[index].id, args)
        .expect("synthetic physical body interprets");
    assert_eq!(outcome.returns, vec![expected]);
}

fn assert_precise(function: &Function, result: &IrTy) {
    assert!(instructions(function).any(|inst| matches!(inst,
        Inst::ExtractField { ty, .. } if ty == result)));
    assert!(!instructions(function).any(|inst| matches!(inst, Inst::Undef { .. })));
}

#[test]
fn physical_marker_field_read_preserves_layout_and_value() {
    let input =
        reader("field_read", marker(), Ty::i32(), &[1], definitions(vec![Ty::u64(), Ty::i32()]));
    let before = serde_json::to_vec(&input).expect("synthetic input serializes");
    let before_hash = input.content_hash();
    let module = lower_to_trust_ir(&input).expect("physical marker field read lowers");
    valid(&module);
    assert_eq!(serde_json::to_vec(&input).expect("input serializes"), before);
    assert_eq!(
        input.content_hash(),
        before_hash,
        "lowering must not rewrite source/cache identity"
    );
    assert_precise(&module.functions[0], &IrTy::I32);
    let ty = argument_type(&module.functions[0]);
    let IrTy::Struct(id) = ty else { panic!("physical argument must be a struct") };
    let layout = module.structs.iter().find(|item| item.id == id).expect("registered struct");
    assert_eq!((layout.size, layout.align), (Some(16), Some(8)));
    assert_eq!(
        layout.fields.iter().map(|field| field.offset).collect::<Vec<_>>(),
        vec![Some(0), Some(8)]
    );
    assert_eq!(
        layout.fields.iter().map(|field| field.ty.clone()).collect::<Vec<_>>(),
        vec![IrTy::U64, IrTy::I32]
    );
    returns(
        &module,
        0,
        vec![aggregate(IrTy::Struct(id), vec![integer(IrTy::U64, 9), integer(IrTy::I32, 41)])],
        integer(IrTy::I32, 41),
    );
}

#[test]
fn physical_copy_and_field_store_preserve_independent_values() {
    for (read_local, read_field, expected) in [(1, 0, 99), (2, 0, 11), (1, 1, 22)] {
        let mut input = reader(
            "construct_copy_store",
            marker(),
            Ty::i64(),
            &[0],
            definitions(vec![Ty::i64(), Ty::i64()]),
        );
        input.body.locals.push(LocalDecl { index: 2, ty: marker(), name: Some("copy".into()) });
        input.body.blocks[0].stmts = vec![
            assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
            assign(field(1, &[0]), Rvalue::Use(Operand::Constant(ConstValue::Int(99)))),
            assign(Place::local(0), Rvalue::Use(Operand::Copy(field(read_local, &[read_field])))),
        ];
        let module = lower_to_trust_ir(&input).expect("physical copy and update lower");
        valid(&module);
        assert!(
            instructions(&module.functions[0]).any(|inst| matches!(inst, Inst::InsertField { .. }))
        );
        assert!(
            instructions(&module.functions[0])
                .any(|inst| matches!(inst, Inst::ExtractField { ty: IrTy::I64, .. }))
        );
        assert!(!instructions(&module.functions[0]).any(|inst| matches!(inst, Inst::Undef { .. })));
        let ty = argument_type(&module.functions[0]);
        returns(
            &module,
            0,
            vec![aggregate(ty, vec![integer(IrTy::I64, 11), integer(IrTy::I64, 22)])],
            integer(IrTy::I64, expected),
        );
    }
}

#[test]
fn physical_construction_executes_as_the_complete_constructor() {
    let mut input =
        reader("construction_boundary", marker(), Ty::i64(), &[0], definitions(vec![Ty::i64()]));
    input.body.arg_count = 0;
    input.body.blocks[0].stmts.insert(
        0,
        assign(
            Place::local(1),
            Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: VALUE.into(),
                    variant: 0,
                    active_field: None,
                    args: None,
                },
                vec![Operand::Constant(ConstValue::Int(11))],
            ),
        ),
    );
    let module = lower_to_trust_ir(&input).expect("structure is recoverable");
    valid(&module);
    // BMC-LANE-1: the construction names its one lane, so it is the canonical
    // complete constructor, exact execution with no seed at all. The former
    // aggregate `Undef` seed under an `InsertField` faulted as aggregate poison;
    // no fabricated zero seed replaced it.
    assert!(
        !instructions(&module.functions[0])
            .any(|inst| matches!(inst, Inst::Undef { .. } | Inst::InsertField { .. }))
    );
    assert!(instructions(&module.functions[0])
        .any(|inst| matches!(inst, Inst::MakeAggregate { variant: None, fields, .. } if fields.len() == 1)));
    returns(&module, 0, vec![], integer(IrTy::I64, 11));
}

#[test]
fn same_marker_uses_each_bodys_scalar_and_layout_in_both_bundle_orders() {
    let integer_reader =
        reader("integer_reader", marker(), Ty::i32(), &[0], definitions(vec![Ty::i32()]));
    let boolean_reader =
        reader("boolean_reader", marker(), Ty::Bool, &[1], definitions(vec![Ty::u64(), Ty::Bool]));
    for reverse in [false, true] {
        let mut inputs = vec![integer_reader.clone(), boolean_reader.clone()];
        if reverse {
            inputs.reverse();
        }
        let module =
            lower_to_trust_ir_functions("body_local_scalars", &inputs).expect("bundle lowers");
        valid(&module);
        let int_index = usize::from(reverse);
        let bool_index = 1 - int_index;
        let int_ty = argument_type(&module.functions[int_index]);
        let bool_ty = argument_type(&module.functions[bool_index]);
        assert_ne!(int_ty, bool_ty, "same name must not conflate different body-local definitions");
        assert_precise(&module.functions[int_index], &IrTy::I32);
        assert_precise(&module.functions[bool_index], &IrTy::Bool);
        returns(
            &module,
            int_index,
            vec![aggregate(int_ty, vec![integer(IrTy::I32, 73)])],
            integer(IrTy::I32, 73),
        );
        returns(
            &module,
            bool_index,
            vec![aggregate(bool_ty, vec![integer(IrTy::U64, 8), InterpretValue::bool(true)])],
            InterpretValue::bool(true),
        );
    }
}

fn assert_missing_table_havoc(function: &Function, extracts: usize) {
    assert_eq!(
        instructions(function).filter(|inst| matches!(inst, Inst::ExtractField { .. })).count(),
        extracts
    );
    assert!(!instructions(function).any(|inst| matches!(inst, Inst::Assume { .. })));
    assert!(function.blocks.iter().flat_map(|block| &block.body).any(|node| {
        matches!(node.inst, Inst::Undef { ty: IrTy::I32 })
            && node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc)
    }));
}

#[test]
fn absent_table_does_not_borrow_another_bodys_cached_definition() {
    let present = reader("present", marker(), Ty::i32(), &[0], definitions(vec![Ty::i32()]));
    let absent = reader("absent", marker(), Ty::i32(), &[0], DatatypeDefs::new());
    for reverse in [false, true] {
        let mut inputs = vec![present.clone(), absent.clone()];
        if reverse {
            inputs.reverse();
        }
        let module = lower_to_trust_ir_functions("absent_table", &inputs)
            .expect("opaque read remains typed havoc");
        valid(&module);
        let present_index = usize::from(reverse);
        let absent_index = 1 - present_index;
        assert_precise(&module.functions[present_index], &IrTy::I32);
        assert_missing_table_havoc(&module.functions[absent_index], 0);
        let ty = argument_type(&module.functions[present_index]);
        assert_ne!(ty, argument_type(&module.functions[absent_index]));
        returns(
            &module,
            present_index,
            vec![aggregate(ty, vec![integer(IrTy::I32, 77)])],
            integer(IrTy::I32, 77),
        );
    }
}

fn nested_value(module: &Module, index: usize, value: InterpretValue) -> InterpretValue {
    let ty = argument_type(&module.functions[index]);
    let IrTy::Struct(id) = &ty else { panic!("outer struct") };
    let outer = module.structs.iter().find(|item| &item.id == id).expect("outer definition");
    aggregate(ty, vec![aggregate(outer.fields[0].ty.clone(), vec![value])])
}

#[test]
fn nested_wrapper_cache_keys_include_each_bodys_physical_child() {
    let wrapper = structure("synthetic_physical::Wrapper", vec![marker()]);
    let int_reader =
        reader("nested_int", wrapper.clone(), Ty::i32(), &[0, 0], definitions(vec![Ty::i32()]));
    let bool_reader =
        reader("nested_bool", wrapper, Ty::Bool, &[0, 0], definitions(vec![Ty::Bool]));
    for reverse in [false, true] {
        let mut inputs = vec![int_reader.clone(), bool_reader.clone()];
        if reverse {
            inputs.reverse();
        }
        let module =
            lower_to_trust_ir_functions("nested_cache", &inputs).expect("nested bundle lowers");
        valid(&module);
        let int_index = usize::from(reverse);
        let bool_index = 1 - int_index;
        assert_ne!(
            argument_type(&module.functions[int_index]),
            argument_type(&module.functions[bool_index])
        );
        assert_precise(&module.functions[int_index], &IrTy::I32);
        assert_precise(&module.functions[bool_index], &IrTy::Bool);
        returns(
            &module,
            int_index,
            vec![nested_value(&module, int_index, integer(IrTy::I32, 18))],
            integer(IrTy::I32, 18),
        );
        returns(
            &module,
            bool_index,
            vec![nested_value(&module, bool_index, InterpretValue::bool(false))],
            InterpretValue::bool(false),
        );
    }
}

#[test]
fn nested_wrapper_with_absent_table_stays_opaque_in_both_orders() {
    let wrapper = structure("synthetic_physical::Wrapper", vec![marker()]);
    let present =
        reader("nested_present", wrapper.clone(), Ty::i32(), &[0, 0], definitions(vec![Ty::i32()]));
    let absent = reader("nested_absent", wrapper, Ty::i32(), &[0, 0], DatatypeDefs::new());
    for reverse in [false, true] {
        let mut inputs = vec![present.clone(), absent.clone()];
        if reverse {
            inputs.reverse();
        }
        let module = lower_to_trust_ir_functions("nested_absence", &inputs)
            .expect("opaque child remains havoc");
        valid(&module);
        let present_index = usize::from(reverse);
        let absent_index = 1 - present_index;
        assert_precise(&module.functions[present_index], &IrTy::I32);
        // The known wrapper itself can be extracted; its unknown child's
        // alleged field MUST NOT become a second ExtractField.
        assert_missing_table_havoc(&module.functions[absent_index], 1);
        assert_ne!(
            argument_type(&module.functions[present_index]),
            argument_type(&module.functions[absent_index])
        );
        returns(
            &module,
            present_index,
            vec![nested_value(&module, present_index, integer(IrTy::I32, 29))],
            integer(IrTy::I32, 29),
        );
    }
}

#[test]
fn physical_marker_out_of_range_field_is_refused() {
    let input = reader("bad_field", marker(), Ty::i32(), &[1], definitions(vec![Ty::i32()]));
    let error =
        lower_to_trust_ir(&input).expect_err("missing physical field must not become havoc");
    assert!(error.to_string().contains("ADT field 1 out of range"), "{error}");
}

#[test]
fn physical_marker_wrong_field_result_type_remains_explicit_havoc() {
    let input = reader("wrong_field_sort", marker(), Ty::Bool, &[0], definitions(vec![Ty::i32()]));
    match lower_to_trust_ir(&input) {
        Err(_) => {}
        Ok(module) => {
            assert!(
                instructions(&module.functions[0])
                    .any(|inst| matches!(inst, Inst::ExtractField { ty: IrTy::I32, .. }))
            );
            // The existing compatibility lane over-approximates a mismatched
            // copy with a fresh value. Recovery must not turn that into a
            // boolean fact or a precise interpretation of an ill-typed body.
            valid(&module);
            assert_boolean_havoc(&module.functions[0]);
        }
    }
}

fn assert_boolean_havoc(function: &Function) {
    assert!(function.blocks.iter().flat_map(|block| &block.body).any(|node| {
        matches!(node.inst, Inst::Undef { ty: IrTy::Bool })
            && node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc)
    }));
    assert!(!instructions(function).any(|inst| matches!(
        inst,
        Inst::Assume { .. } | Inst::Const { value: trust_ir::Constant::Bool(_), .. }
    )));
}
