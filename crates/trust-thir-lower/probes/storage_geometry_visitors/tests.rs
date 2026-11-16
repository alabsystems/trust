// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Source-coupled visitor controls; no TCX execution or proof authority.
use trust_ir::{StorageLayout, Ty, TyG, TyId, FuncTyId, Module};
use template_source::*;

fn geometries() -> Vec<StorageLayout> {
    vec![StorageLayout::new(0, 1), StorageLayout::new(0, 64),
         StorageLayout::new(16, 8), StorageLayout::new(u64::MAX, 1),
         StorageLayout::new(7, 4)]
}

#[test]
fn storage_geometry_has_no_sentinel_or_hidden_row() {
    for layout in geometries() {
        let mut module = Module::new("storage-walk");
        module.types = vec![Ty::Storage(layout), type_param_sentinel(0)];
        let mut walk = SentinelWalk::new(&module);
        assert!(!walk.ty(&Ty::Storage(layout)));
        assert!(!walk.ty(&Ty::Array(TyId::new(0), 3)));
        assert!(!walk.ty(&Ty::PtrConst(Box::new(Ty::Storage(layout)))));
        assert!(walk.ty(&Ty::Array(TyId::new(1), 3)), "a real sentinel still refuses");
    }
}

#[test]
fn storage_geometry_level_map_preserves_both_u64_fields_and_generic_neighbors() {
    let facts = LaneFacts { params: vec![LaneParam::Type], ..LaneFacts::default() };
    for layout in geometries() {
        assert_eq!(abstract_ty(&Ty::Storage(layout), &facts), Ok(TyG::Storage(layout)));
        let source = Ty::Tuple(vec![Ty::Storage(layout), type_param_sentinel(0)]);
        assert_eq!(abstract_ty(&source, &facts), Ok(TyG::Tuple(vec![
            TyG::Storage(layout), TyG::Ext(trust_ir::TemplateRef::Param(trust_ir::ParamId::new(0)))
        ])));
    }
}

#[test]
fn storage_geometry_join_remap_preserves_geometry_and_still_remaps_real_ids() {
    for layout in geometries() {
        let mut ty = Ty::Tuple(vec![Ty::Storage(layout), Ty::Func(FuncTyId::new(0)),
                                  Ty::Array(TyId::new(0), 2)]);
        remap_general_ty(&mut ty, &[FuncTyId::new(7)], &[TyId::new(9)]).unwrap();
        assert_eq!(ty, Ty::Tuple(vec![Ty::Storage(layout), Ty::Func(FuncTyId::new(7)),
                                     Ty::Array(TyId::new(9), 2)]));
    }
    let mut dangling = Ty::Array(TyId::new(0), 2);
    assert!(remap_general_ty(&mut dangling, &[], &[]).is_err());
}

#[test]
fn storage_geometry_mapping_does_not_authorize_by_value_or_invalid_geometry() {
    for layout in geometries() {
        let mut module = Module::new("storage-refusal");
        let mut ty = Ty::Storage(layout);
        remap_general_ty(&mut ty, &[], &[]).unwrap();
        module.add_func_type(trust_ir::FuncTy::unrecorded(vec![ty], vec![], false)).unwrap();
        assert!(trust_ir_build::validate_module(&module).iter().any(|error|
            matches!(error, trust_ir_build::ValidationError::InvalidStorageUse { .. })));
    }
    let mut builder = trust_ir_build::ModuleBuilder::new("storage-allocation");
    let sig = builder.add_func_type(vec![], vec![]);
    let mut body = builder.function("allocate", sig);
    let block = body.create_block(); body.switch_to_block(block); body.set_entry(block);
    body.alloca(Ty::Storage(StorageLayout::new(16, 8)));
    body.ret(vec![]); body.build();
    assert!(trust_ir_build::validate_module(&builder.build().unwrap()).is_empty());
}
