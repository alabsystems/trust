use trust_ir::{
    Block, BlockId, Constant, FieldDef, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode,
    Module, StructDef, StructId, StructRepr, Ty, TyId, ValueId,
};

use super::element_bound;

fn definition(id: u32) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("Element{id}"),
        fields: vec![FieldDef { name: "word".into(), ty: Ty::U64, offset: Some(0) }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    }
}

#[test]
fn zero_array_struct_requires_exact_positional_id_and_strictly_earlier_definition() {
    let types = [Ty::Struct(StructId::new(0)), Ty::Struct(StructId::new(1))];
    let mut structs = [definition(0), definition(1)];
    assert_eq!(element_bound(&types, &structs, TyId::new(0), 1), Some(1));
    assert_eq!(element_bound(&types, &structs, TyId::new(1), 2), Some(2));
    assert_eq!(element_bound(&types, &structs, TyId::new(0), 0), None, "self");
    assert_eq!(element_bound(&types, &structs, TyId::new(1), 1), None, "self");
    assert_eq!(element_bound(&types, &structs, TyId::new(1), 0), None, "forward");
    structs[0].id = StructId::new(1);
    assert_eq!(element_bound(&types, &structs, TyId::new(0), 1), None, "wrong row ID");
}

#[test]
fn zero_array_struct_dangling_entries_and_every_other_indexed_kind_stay_closed() {
    let structs = [definition(0)];
    assert_eq!(element_bound(&[], &structs, TyId::new(0), 1), None);
    assert_eq!(element_bound(&[Ty::Struct(StructId::new(0))], &[], TyId::new(0), 1), None);
    assert_eq!(element_bound(&[Ty::Struct(StructId::new(9))], &structs, TyId::new(0), 10), None);
    let other_elements = [
        Ty::Func(FuncTyId::new(0)),
        Ty::Enum(trust_ir::EnumId::new(0)),
        Ty::Closure(trust_ir::ClosureTyId::new(0)),
        Ty::Array(TyId::new(0), 0),
        Ty::Ref(Box::new(Ty::Struct(StructId::new(0)))),
        Ty::Tuple(vec![Ty::Struct(StructId::new(0)), Ty::U8]),
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(TyId::new(0))),
        Ty::Unit,
        Ty::U8,
    ];
    for element in other_elements {
        assert_eq!(
            element_bound(&[element.clone()], &structs, TyId::new(0), 1),
            None,
            "this additional lane only admits an exact struct: {element:?}"
        );
    }
}

#[test]
fn zero_array_struct_retains_its_real_element_type_and_alignment() {
    let mut module = Module::new("zero_array_struct_layout");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let id = module.add_struct_def(definition(0)).unwrap();
    let element = module.add_type(Ty::Struct(id)).unwrap();
    assert_eq!(element_bound(&module.types, &module.structs, element, 1), Some(1));
    let array = Ty::Array(element, 0);
    let layout = module.ty_layout_shape(&array).unwrap();
    assert_eq!(layout.size_bytes(), Some(0));
    assert_eq!(layout.align_bits, Some(64));
    assert_eq!(module.types[element.as_usize()], Ty::Struct(id));
    assert_eq!(array, Ty::Array(element, 0));
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![array.clone()],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "empty_array", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const { ty: array, value: Constant::Array(vec![]) })
            .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "the real zero-array module must validate: {errors:?}");
}
