//! Physical struct constructors must not interpret user field names as enum
//! metadata. These synthetic inputs test the production lowering, not the Rust
//! extractor. A complete construction is one `MakeAggregate`, which the reference
//! interpreter executes (BMC-LANE-1); no interpreter or proof authority is
//! changed here.

use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty as IrTy;
use trust_ir::{Constant, Module, ValueId};
use trust_ir_build::validate_module;
use trust_types::{
    AdtKind, AdtLayoutInfo, AggregateKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand,
    Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use crate::lower::lower_to_trust_ir;

const NAME: &str = "physical_constructor::Structure";

fn fixture(names: &[&str], operands: Vec<Operand>, marker: bool) -> VerifiableFunction {
    let fields = names.iter().map(|name| ((*name).into(), Ty::i64())).collect();
    let physical = Ty::Adt {
        name: NAME.into(),
        fields,
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: Some(Box::new(AdtLayoutInfo {
            size: names.len() as u64 * 8,
            align: 8,
            field_offsets: (0..names.len() as u64).map(|index| index * 8).collect(),
            repr: "c".into(),
        })),
        enum_layout: None,
        adt_kind: Some(AdtKind::Struct),
    };
    let result = if marker {
        Ty::Datatype { name: NAME.into(), variants: vec![] }
    } else {
        physical.clone()
    };
    let mut locals = vec![LocalDecl { index: 0, ty: result.clone(), name: None }];
    locals.extend((1..=names.len()).map(|index| LocalDecl {
        index,
        ty: Ty::i64(),
        name: Some(format!("argument_{index}")),
    }));
    VerifiableFunction {
        name: "constructor".into(),
        def_path: "physical_constructor::constructor".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: NAME.into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        operands,
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: names.len(),
            return_ty: result,
            datatype_defs: [(NAME.into(), physical)].into(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn copies(count: usize) -> Vec<Operand> {
    (1..=count).map(|index| Operand::Copy(Place::local(index))).collect()
}

fn lower(input: &VerifiableFunction) -> Module {
    let module = lower_to_trust_ir(input).expect("physical constructor lowers");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "invalid constructor: {errors:?}");
    module
}

/// `(lane, value)` for every lane the construction writes: the operands of its
/// one complete constructor, in lane order. A poison seed under an insert chain
/// is not a construction (it is unexecutable), so none may remain.
fn insertions(module: &Module) -> Vec<(u32, ValueId)> {
    let nodes = || module.functions[0].blocks.iter().flat_map(|block| &block.body);
    assert!(
        !nodes().any(|node| matches!(node.inst, Inst::Undef { .. } | Inst::InsertField { .. })),
        "a complete construction has no aggregate seed"
    );
    let constructors: Vec<_> = nodes()
        .filter_map(|node| match &node.inst {
            Inst::MakeAggregate { variant: None, fields, .. } => Some(fields),
            _ => None,
        })
        .collect();
    match constructors.as_slice() {
        // A zero-lane structure is a unit-like constant: it writes no lane.
        [] => Vec::new(),
        [lanes] => lanes.iter().enumerate().map(|(lane, value)| (lane as u32, *value)).collect(),
        more => panic!("one complete constructor expected, found {}", more.len()),
    }
}

#[test]
fn physical_struct_field_names_preserve_parameter_order_inline_and_by_marker() {
    let names = ["tag", "discriminant", "__tag", "__v0_payload", "__v1_payload", "other"];
    for marker in [false, true] {
        let input = fixture(&names, copies(names.len()), marker);
        let before = serde_json::to_vec(&input).expect("source serializes");
        let module = lower(&input);
        let entry = module.functions[0]
            .blocks
            .iter()
            .find(|block| block.id == module.functions[0].entry)
            .expect("entry block");
        let expected: Vec<_> = entry
            .params
            .iter()
            .enumerate()
            .map(|(index, (value, _))| (index as u32, *value))
            .collect();
        assert_eq!(insertions(&module), expected, "marker={marker}");
        assert_eq!(serde_json::to_vec(&input).expect("source serializes"), before);
        assert!(!entry.body.iter().any(|node| matches!(node.inst, Inst::Const { .. })));
    }
}

#[test]
fn physical_struct_tag_constants_are_source_operands_not_variant_numbers() {
    let mut input = fixture(
        &["tag", "discriminant", "__v1_payload"],
        [11, 22, 33].map(|value| Operand::Constant(ConstValue::Int(value))).into(),
        true,
    );
    input.body.arg_count = 0;
    input.body.locals.truncate(1);
    let module = lower(&input);
    let nodes: Vec<_> = module.functions[0].blocks.iter().flat_map(|block| &block.body).collect();
    let values: Vec<_> = insertions(&module)
        .iter()
        .map(|(field, value)| {
            let node = nodes
                .iter()
                .find(|node| node.results.as_slice() == [*value])
                .expect("value definition");
            let Inst::Const { value: Constant::Int(value), .. } = node.inst else {
                panic!("expected exact source constant, found {:?}", node.inst)
            };
            (*field, value)
        })
        .collect();
    assert_eq!(values, vec![(0, 11), (1, 22), (2, 33)]);

    // BMC-LANE-1: the exact field assignment is now executable origination. The
    // former spelling, an aggregate `Undef` seed under an `InsertField` chain,
    // faulted as aggregate poison at the seed; the complete constructor runs and
    // returns exactly the source constants, with no narrowing `Assume`.
    assert!(!nodes.iter().any(|node| matches!(node.inst, Inst::Assume { .. })));
    let outcome = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![])
        .expect("the complete construction executes");
    let [returned] = outcome.returns.as_slice() else {
        panic!("one returned value, got {:?}", outcome.returns)
    };
    let expected: Vec<_> = [11, 22, 33]
        .map(|value| InterpretValue::int(IrTy::I64, value).expect("fixture integer fits"))
        .into();
    assert!(
        matches!(&returned.kind, InterpretValueKind::Aggregate(lanes) if *lanes == expected),
        "{returned:?}"
    );
}

#[test]
fn physical_struct_constructor_rejects_missing_and_extra_operands() {
    for marker in [false, true] {
        for count in [1, 3] {
            let operands =
                (0..count).map(|value| Operand::Constant(ConstValue::Int(value))).collect();
            let input = fixture(&["tag", "payload"], operands, marker);
            let error = lower_to_trust_ir(&input).expect_err("arity mismatch must not lower");
            assert!(
                error.to_string().contains(&format!("construction arity {count} != 2")),
                "{error:?}"
            );
        }
    }
}

#[test]
fn physical_struct_constructor_rejects_nonzero_variant_index() {
    let mut input = fixture(&["tag"], copies(1), true);
    let Statement::Assign {
        rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, _), ..
    } = &mut input.body.blocks[0].stmts[0]
    else {
        panic!("fixture constructor")
    };
    *variant = 1;
    let error = lower_to_trust_ir(&input).expect_err("struct has only variant zero");
    assert!(error.to_string().contains("construction carries enum variant 1"), "{error:?}");
}

#[test]
fn physical_empty_struct_keeps_exact_construction_and_checks_arity() {
    // A bare marker's empty table entry intentionally does not resolve under
    // datatype_marker_definition: exercise the actual inline physical type.
    let input = fixture(&[], vec![], false);
    let module = lower(&input);
    let result = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![])
        .expect("empty physical structure remains executable");
    assert_eq!(result.returns.len(), 1);
    assert!(insertions(&module).is_empty());
    let malformed = fixture(&[], vec![Operand::Constant(ConstValue::Int(9))], false);
    let error = lower_to_trust_ir(&malformed).expect_err("empty structure has no operands");
    assert!(error.to_string().contains("construction arity 1 != 0"), "{error:?}");
}
