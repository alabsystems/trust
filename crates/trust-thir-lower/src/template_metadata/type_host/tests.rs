//! Pure remap controls. These images never stand in for a real Rustc Type image.
use super::*;
use trust_ir::{Endianness, FieldDef, StructDef, StructId, StructPassingPolicy, StructRepr,
    TargetInfo, TupleLayoutDescriptor, TyId};

fn module(name: &str) -> Module {
    let mut m = Module::new(name);
    m.target_info = Some(TargetInfo { triple: "aarch64-apple-darwin".into(), pointer_size: 8,
        endianness: Endianness::Little, abi: None, struct_passing: StructPassingPolicy::NativeC });
    m
}
fn image() -> (Module, Vec<Ty>) {
    let mut m = module("source_type_data");
    m.types.push(Ty::U16);
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U16]);
    m.types.push(tuple.clone());
    m.tuple_layouts.push(TupleLayoutDescriptor { tuple_type: TyId::new(1),
        size: 4, align: 2, field_offsets: vec![0, 2] });
    m.structs.push(StructDef { id: StructId::new(0), name: "same_spelling".into(),
        fields: vec![FieldDef { name: "items".into(), ty: Ty::Array(TyId::new(0), 3), offset: Some(0) }],
        size: Some(6), align: Some(2), repr: StructRepr::C, origin: None });
    (m, vec![Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 4), tuple])
}
fn host() -> Module {
    let mut m = module("existing_construction");
    m.types.push(Ty::U64);
    m.structs.push(StructDef { id: StructId::new(0), name: "same_spelling".into(),
        fields: vec![FieldDef { name: "old".into(), ty: Ty::U64, offset: Some(0) }],
        size: Some(8), align: Some(8), repr: StructRepr::C, origin: None });
    m
}

#[test]
fn s_type_table_host_canonical_roots_remap_every_table_context() {
    let host = host(); let before = host.clone(); let (source, roots) = image();
    let result = merge_image(&host, &source, &roots).unwrap();
    assert_eq!(host, before);
    assert_eq!(result.roots()[0], Ty::Struct(StructId::new(1)));
    assert_eq!(result.roots()[1], Ty::Array(TyId::new(1), 4));
    assert_eq!(result.module.structs[1].fields[0].ty, Ty::Array(TyId::new(1), 3));
    assert_eq!(result.module.tuple_layouts[0].tuple_type, TyId::new(2));
    assert_eq!(result.module.types[2], roots[2]);
    assert_eq!(result.module.structs[0], host.structs[0]);
    assert!(trust_ir_build::validate::validate_module(&result.module).is_empty());
    assert!(result.module.functions.is_empty() && result.module.proof_obligations.is_empty());
}

#[test]
fn s_type_table_host_canonical_nominal_reuse_requires_full_rows() {
    let (source, roots) = image();
    let first = merge_image(&module("host"), &source, &roots).unwrap();
    let second = merge_image(first.module(), &source, &roots).unwrap();
    assert_eq!(first.roots(), second.roots());
    assert_eq!(second.module.structs.len(), 1);
    let mut changed = source.clone();
    changed.structs[0].fields[0].name = "different_field".into();
    let distinct = merge_image(first.module(), &changed, &roots).unwrap();
    assert_eq!(distinct.module.structs.len(), 2, "same symbol is no nominal identity");
    assert_ne!(distinct.roots()[0], first.roots()[0]);
}

#[test]
fn s_type_table_host_refuses_target_dangling_root_and_foreign_state_transactionally() {
    let host = host(); let before = host.clone(); let (source, roots) = image();
    for mutation in 0..5 {
        let mut image = source.clone(); let mut requested = roots.clone();
        match mutation {
            0 => image.target_info.as_mut().unwrap().pointer_size = 4,
            1 => requested[0] = Ty::Array(TyId::new(99), 1),
            2 => image.structs[0].fields[0].offset = Some(99),
            3 => image.files.push("source-with-file-state".into()),
            _ => { image.func_types.push(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None }); }
        }
        assert!(merge_image(&host, &image, &requested).is_err(), "mutation {mutation}");
        assert_eq!(host, before);
    }
}

#[test]
fn s_type_table_host_partial_generic_placeholders_remain_for_final_validator() {
    let mut host = host();
    host.func_types.push(FuncTy { params: vec![Ty::Error], returns: vec![Ty::Error], is_vararg: false, abi: None });
    let (source, roots) = image();
    let result = merge_image(&host, &source, &roots).unwrap();
    assert_eq!(result.module.func_types[0], host.func_types[0]);
    assert!(!trust_ir_build::validate::validate_module(&result.module).is_empty(),
        "this is explicitly partial construction, never a validator bypass");
}

#[test]
fn s_type_table_host_enum_fields_and_discriminants_share_the_canonical_remap() {
    use trust_ir::{EnumDef, EnumId, EnumVariant};
    let (mut source, mut roots) = image();
    let mut row = EnumDef::new(EnumId::new(0), "same_enum", vec![EnumVariant {
        name: "Payload".into(), fields: vec![Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 2)],
        field_names: vec!["nominal".into(), "array".into()],
    }]);
    row.discriminants = vec![Some(7)]; source.enums.push(row);
    roots.push(Ty::Enum(EnumId::new(0)));
    let mut host = host();
    host.enums.push(EnumDef::new(EnumId::new(0), "same_enum", vec![EnumVariant {
        name: "Different".into(), fields: vec![Ty::U64], field_names: vec![],
    }]));
    let result = merge_image(&host, &source, &roots).unwrap();
    assert_eq!(result.roots()[3], Ty::Enum(EnumId::new(1)));
    let row = &result.module.enums[1];
    assert_eq!(row.variants[0].fields, vec![Ty::Struct(StructId::new(1)), Ty::Array(TyId::new(1), 2)]);
    assert_eq!(row.discriminants, vec![Some(7)]);
    assert_eq!(row.variants[0].field_names, vec!["nominal", "array"]);
    assert_eq!(result.module.enums[0], host.enums[0]);
    assert!(trust_ir_build::validate::validate_module(result.module()).is_empty());
}
