use trust_ir::{Block, BlockId, ClosureTyId, Endianness, FuncTy, Function, TargetInfo};

use super::*;
fn fixture() -> Module {
    let mut m = Module::new("native_carrier");
    m.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    let sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0))],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(0), "body", sig, BlockId::new(0));
    f.blocks.push(Block::new(BlockId::new(0)));
    m.functions.push(f);
    m
}
#[test]
fn native_carrier_requires_complete_aggregate_coverage() {
    let source = fixture();
    let mut out = source.clone();
    assert!(classify(&source, &mut out, &[]).is_err());
    assert_eq!(out, source);
    classify(&source, &mut out, &[(&source, FuncId::new(0))]).unwrap();
    assert_eq!(out.target_info.as_ref().unwrap().struct_passing, StructPassingPolicy::NativeC);
    out.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::Unclassified;
    assert_eq!(out, source);
    let mut extra = source.clone();
    extra.func_types.push(extra.func_types[0].clone());
    assert!(classify(&extra, &mut extra.clone(), &[(&extra, FuncId::new(0))]).is_err());
}
#[test]
fn native_carrier_rejects_changed_bodies_or_evidence() {
    let source = fixture();
    let checked = [(&source, FuncId::new(0))];
    let mut changed = source.clone();
    changed.functions[0].blocks.clear();
    assert!(classify(&source, &mut changed, &checked).is_err());
    let mut changed = source.clone();
    changed.files.push("extra-source.rs".into());
    assert!(classify(&source, &mut changed, &checked).is_err());
    let mut changed = source.clone();
    changed.target_info.as_mut().unwrap().pointer_size = 4;
    assert!(classify(&source, &mut changed, &checked).is_err());
}
#[test]
fn native_carrier_rejects_another_image_and_shared_unchecked_body() {
    let source = fixture();
    let foreign = source.clone();
    assert!(classify(&source, &mut source.clone(), &[(&foreign, FuncId::new(0))]).is_err());
    assert!(
        classify(
            &source,
            &mut source.clone(),
            &[(&source, FuncId::new(0)), (&source, FuncId::new(0))]
        )
        .is_err()
    );
    let mut flat_adapter = source.clone();
    let sig = flat_adapter
        .add_func_type(FuncTy {
            params: vec![Ty::Isize, Ty::Usize, Ty::Char],
            returns: vec![Ty::Usize],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(1), "flat_adapter", sig, BlockId::new(0));
    f.blocks.push(Block::new(BlockId::new(0)));
    flat_adapter.functions.push(f);
    classify(&flat_adapter, &mut flat_adapter.clone(), &[(&flat_adapter, FuncId::new(0))]).unwrap();
    let mut shared = source.clone();
    let mut unchecked = shared.functions[0].clone();
    unchecked.id = FuncId::new(1);
    unchecked.name = "unchecked".into();
    shared.functions.push(unchecked);
    assert!(classify(&shared, &mut shared.clone(), &[(&shared, FuncId::new(0))]).is_err());
    classify(&shared, &mut shared.clone(), &[(&shared, FuncId::new(0)), (&shared, FuncId::new(1))])
        .unwrap();
}

#[test]
fn fp_signatures_still_require_every_original_source_body_witness() {
    for ty in [Ty::F32, Ty::F64] {
        let mut source = fixture();
        source.func_types[0].params = vec![ty.clone()];
        source.func_types[0].returns = vec![ty];
        assert!(classify(&source, &mut source.clone(), &[]).is_err());
        classify(&source, &mut source.clone(), &[(&source, FuncId::new(0))]).unwrap();
        let another_image = source.clone();
        assert!(classify(&source, &mut source.clone(), &[(&another_image, FuncId::new(0))]).is_err());
        let mut extra = source.functions[0].clone();extra.id = FuncId::new(1);extra.name = "unwitnessed_fp".into();source.functions.push(extra);
        assert!(classify(&source, &mut source.clone(), &[(&source, FuncId::new(0))]).is_err());
    }
}
