//! Pure remap controls. These images never stand in for a real Rustc Type image.
use trust_ir::{
    Endianness, FieldDef, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    TupleLayoutDescriptor, TyId,
};

use super::*;

fn module(name: &str) -> Module {
    let mut m = Module::new(name);
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    m
}
fn image() -> (Module, Vec<Ty>) {
    let mut m = module("source_type_data");
    m.types.push(Ty::U16);
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U16]);
    m.types.push(tuple.clone());
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(1),
        size: 4,
        align: 2,
        field_offsets: vec![0, 2],
    });
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "same_spelling".into(),
        fields: vec![FieldDef {
            name: "items".into(),
            ty: Ty::Array(TyId::new(0), 3),
            offset: Some(0),
        }],
        size: Some(6),
        align: Some(2),
        repr: StructRepr::C,
        origin: None,
    });
    (m, vec![Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 4), tuple])
}
fn host() -> Module {
    let mut m = module("existing_construction");
    m.types.push(Ty::U64);
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "same_spelling".into(),
        fields: vec![FieldDef { name: "old".into(), ty: Ty::U64, offset: Some(0) }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    m
}

#[test]
fn s_type_table_host_canonical_roots_remap_every_table_context() {
    let host = host();
    let before = host.clone();
    let (source, roots) = image();
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
    let host = host();
    let before = host.clone();
    let (source, roots) = image();
    for mutation in 0..6 {
        let mut image = source.clone();
        let mut requested = roots.clone();
        match mutation {
            0 => image.target_info.as_mut().unwrap().pointer_size = 4,
            1 => requested[0] = Ty::Array(TyId::new(99), 1),
            2 => image.structs[0].fields[0].offset = Some(99),
            3 => image.files.push("source-with-file-state".into()),
            4 => {
                image.func_types.push(FuncTy {
                    params: vec![],
                    returns: vec![],
                    is_vararg: false,
                    abi: None,
                });
                image.functions.push(trust_ir::Function::new(
                    trust_ir::FuncId::new(0),
                    "foreign_executable_body",
                    trust_ir::FuncTyId::new(0),
                    trust_ir::BlockId::new(0),
                ));
            }
            _ => image.blobs.push(trust_ir::blob::Blob::new(vec![1, 2, 3])),
        }
        assert!(merge_image(&host, &image, &requested).is_err(), "mutation {mutation}");
        assert_eq!(host, before);
    }
}

#[test]
fn s_type_table_host_transports_closure_frames_and_signatures_without_bodies() {
    use trust_ir::{ClosureLayoutDescriptor, ClosureTy, ClosureTyId, FuncTyId};
    let (mut source, _) = image();
    let roots = vec![Ty::Closure(ClosureTyId::new(0)), Ty::Func(FuncTyId::new(1))];
    source.func_types = vec![
        FuncTy { params: roots.clone(), returns: vec![], is_vararg: false, abi: None },
        FuncTy { params: vec![Ty::U16], returns: vec![Ty::U64], is_vararg: false, abi: None },
    ];
    source.closure_types.push(ClosureTy {
        func: FuncTyId::new(1),
        captures: vec![Ty::Struct(StructId::new(0)), Ty::U16],
    });
    source.closure_layouts.push(ClosureLayoutDescriptor {
        closure: ClosureTyId::new(0),
        size: 8,
        align: 2,
        capture_offsets: vec![0, 6],
        origin: None,
    });
    let mut host = host();
    host.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    host.closure_types.push(ClosureTy { func: FuncTyId::new(0), captures: vec![Ty::U64] });
    host.closure_layouts.push(ClosureLayoutDescriptor {
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
        origin: None,
    });
    let original = host.clone();
    let result = merge_image(&host, &source, &roots).unwrap();
    assert_eq!(host, original, "placement is transactional");
    let Ty::Closure(id) = result.roots()[0] else { panic!("closure root lost") };
    assert_ne!(id, ClosureTyId::new(0));
    let closure = &result.module().closure_types[id.as_usize()];
    assert_eq!(closure.captures, vec![Ty::Struct(StructId::new(1)), Ty::U16]);
    assert_eq!(result.roots()[1], Ty::Func(closure.func));
    let signature = result.module().func_type(closure.func).unwrap();
    assert_eq!(signature.params, vec![Ty::U16]);
    assert_eq!(signature.returns, vec![Ty::U64]);
    let layout = result.module().closure_layouts.iter().find(|row| row.closure == id).unwrap();
    assert_eq!(layout.capture_offsets, vec![0, 6]);
    assert_eq!((layout.size, layout.align), (8, 2));
    assert!(trust_ir_build::validate::validate_module(result.module()).is_empty());
    assert!(
        result.module().functions.is_empty()
            && result.module().globals.is_empty()
            && result.module().drop_glue.is_empty()
            && result.module().proof_obligations.is_empty()
    );
    let mut invalid = source;
    invalid.closure_layouts[0].capture_offsets[1] = 4;
    assert!(merge_image(&host, &invalid, &roots).is_err(), "overlapping source frame refused");
    assert_eq!(host, original);
}

#[test]
fn s_type_table_host_partial_generic_placeholders_remain_for_final_validator() {
    let mut host = host();
    host.func_types.push(FuncTy {
        params: vec![Ty::Error],
        returns: vec![Ty::Error],
        is_vararg: false,
        abi: None,
    });
    let (source, roots) = image();
    let result = merge_image(&host, &source, &roots).unwrap();
    assert_eq!(result.module.func_types[0], host.func_types[0]);
    assert!(
        !trust_ir_build::validate::validate_module(&result.module).is_empty(),
        "this is explicitly partial construction, never a validator bypass"
    );
}

#[test]
fn s_type_table_host_enum_fields_and_discriminants_share_the_canonical_remap() {
    use trust_ir::{EnumDef, EnumId, EnumVariant};
    let (mut source, mut roots) = image();
    let mut row = EnumDef::new(
        EnumId::new(0),
        "same_enum",
        vec![EnumVariant {
            name: "Payload".into(),
            fields: vec![Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 2)],
            field_names: vec!["nominal".into(), "array".into()],
        }],
    );
    row.discriminants = vec![Some(7)];
    source.enums.push(row);
    roots.push(Ty::Enum(EnumId::new(0)));
    let mut host = host();
    host.enums.push(EnumDef::new(
        EnumId::new(0),
        "same_enum",
        vec![EnumVariant { name: "Different".into(), fields: vec![Ty::U64], field_names: vec![] }],
    ));
    let result = merge_image(&host, &source, &roots).unwrap();
    assert_eq!(result.roots()[3], Ty::Enum(EnumId::new(1)));
    let row = &result.module.enums[1];
    assert_eq!(
        row.variants[0].fields,
        vec![Ty::Struct(StructId::new(1)), Ty::Array(TyId::new(1), 2)]
    );
    assert_eq!(row.discriminants, vec![Some(7)]);
    assert_eq!(row.variants[0].field_names, vec!["nominal", "array"]);
    assert_eq!(result.module.enums[0], host.enums[0]);
    assert!(trust_ir_build::validate::validate_module(result.module()).is_empty());
}
