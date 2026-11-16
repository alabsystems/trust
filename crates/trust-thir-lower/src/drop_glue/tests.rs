//! Trust (step 2 increment 4c): the pure half of the glue producer — synthesis, executed by the
//! reference interpreter (`drop_glue_oracle::run_synthesized`), the rewrite and its postcondition.
//! Each test fails before the change that adds the function it exercises.

use trust_ir::{BlockId, FuncId, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::*;
use crate::drop_glue_oracle::{ExecutedCall, GlueRun, run_synthesized};

fn child(field: u32, offset: u64, glue: &str) -> GlueChild<String> {
    GlueChild { field, offset, glue: glue.to_string() }
}

fn run(shape: &GlueShape<String>, size: u64, tag: Option<(u64, u32, u128)>) -> Vec<ExecutedCall> {
    run_synthesized("glue", shape, &GlueRun { size, align: 8, tag, elements: None })
        .unwrap_or_else(|why| panic!("the glue did not execute: {why}"))
}

fn call(name: &str, offset: u64) -> ExecutedCall {
    (name.to_string(), offset, None)
}

#[test]
fn a_struct_glue_calls_the_destructor_then_each_field_in_declaration_order() {
    let shape = GlueShape::Fields {
        dtor: Some("S::drop".to_string()),
        fields: vec![child(1, 8, "glue_a"), child(2, 0, "glue_b"), child(4, 12, "glue_a")],
    };
    assert_eq!(
        run(&shape, 16, None),
        vec![call("S::drop", 0), call("glue_a", 8), call("glue_b", 0), call("glue_a", 12)]
    );
}

#[test]
fn a_noop_glue_calls_nothing_and_a_dtor_only_glue_calls_only_the_destructor() {
    assert_eq!(run(&GlueShape::Noop, 1, None), Vec::<ExecutedCall>::new());
    let dtor_only = GlueShape::Fields { dtor: Some("U::drop".to_string()), fields: vec![] };
    assert_eq!(run(&dtor_only, 4, None), vec![call("U::drop", 0)]);
}

fn direct_enum() -> GlueShape<String> {
    // enum E { A(X) = 0, B(u8, Y, X) = 7, C = 9 } with a u8 tag at offset 0.
    GlueShape::Enum {
        dtor: Some("E::drop".to_string()),
        tag: Some(TagDecode {
            offset: 0,
            bits: 8,
            scheme: TagScheme::Direct { tags: vec![(0, 0), (1, 7), (2, 9)] },
        }),
        untagged_index: u32::MAX,
        arms: vec![
            GlueArm { variant: 0, fields: vec![child(0, 4, "glue_x")] },
            GlueArm { variant: 1, fields: vec![child(1, 8, "glue_y"), child(2, 4, "glue_x")] },
        ],
    }
}

#[test]
fn a_direct_tag_enum_glue_drops_exactly_the_decoded_variant() {
    let shape = direct_enum();
    assert_eq!(run(&shape, 16, Some((0, 8, 0))), vec![call("E::drop", 0), call("glue_x", 4)]);
    assert_eq!(
        run(&shape, 16, Some((0, 8, 7))),
        vec![call("E::drop", 0), call("glue_y", 8), call("glue_x", 4)]
    );
    // A variant with no needs-drop field runs the destructor only.
    assert_eq!(run(&shape, 16, Some((0, 8, 9))), vec![call("E::drop", 0)]);
}

#[test]
fn a_direct_tag_is_compared_at_the_tags_width() {
    // `#[repr(i16)] enum { A(X) = -1, B = 0 }`: the tag is 0xffff at offset 2.
    let shape = GlueShape::Enum {
        dtor: None,
        tag: Some(TagDecode {
            offset: 2,
            bits: 16,
            scheme: TagScheme::Direct { tags: vec![(0, 0xffff), (1, 0)] },
        }),
        untagged_index: u32::MAX,
        arms: vec![GlueArm { variant: 0, fields: vec![child(0, 4, "glue_x")] }],
    };
    assert_eq!(run(&shape, 8, Some((2, 16, 0xffff))), vec![call("glue_x", 4)]);
    assert_eq!(run(&shape, 8, Some((2, 16, 0))), Vec::<ExecutedCall>::new());
}

fn niche_enum(niche_start: u128) -> GlueShape<String> {
    // Three variants: 0 and 1 in the niche, 2 untagged (its payload holds the tag byte at 0).
    GlueShape::Enum {
        dtor: None,
        tag: Some(TagDecode {
            offset: 0,
            bits: 8,
            scheme: TagScheme::Niche { untagged: 2, start: 0, end: 1, niche_start },
        }),
        untagged_index: 2,
        arms: vec![
            GlueArm { variant: 1, fields: vec![child(0, 8, "glue_v1")] },
            GlueArm { variant: 2, fields: vec![child(0, 0, "glue_v2"), child(1, 8, "glue_w")] },
        ],
    }
}

#[test]
fn a_niche_enum_glue_decodes_rustcs_niche_encoding() {
    let shape = niche_enum(254);
    // tag = (v - start) + niche_start: 254 is variant 0 (no drop), 255 variant 1.
    assert_eq!(run(&shape, 16, Some((0, 8, 254))), Vec::<ExecutedCall>::new());
    assert_eq!(run(&shape, 16, Some((0, 8, 255))), vec![call("glue_v1", 8)]);
    // Anything outside the niche range is the untagged variant.
    for tag in [0u128, 1, 7, 253] {
        assert_eq!(
            run(&shape, 16, Some((0, 8, tag))),
            vec![call("glue_v2", 0), call("glue_w", 8)],
            "tag {tag}"
        );
    }
}

#[test]
fn a_niche_range_that_wraps_the_tags_width_decodes_with_wrapping_arithmetic() {
    let shape = niche_enum(255);
    assert_eq!(run(&shape, 16, Some((0, 8, 255))), Vec::<ExecutedCall>::new());
    // 255 + 1 wraps to 0 at the tag's width: variant 1.
    assert_eq!(run(&shape, 16, Some((0, 8, 0))), vec![call("glue_v1", 8)]);
    assert_eq!(run(&shape, 16, Some((0, 8, 1))), vec![call("glue_v2", 0), call("glue_w", 8)]);
}

#[test]
fn an_untagged_enum_glue_drops_only_the_inhabited_variant() {
    // `Variants::Single { index: 1 }`: variant 0 is uninhabited; its arm is never taken.
    let shape = GlueShape::Enum {
        dtor: None,
        tag: None,
        untagged_index: 1,
        arms: vec![
            GlueArm { variant: 0, fields: vec![child(0, 0, "glue_never")] },
            GlueArm { variant: 1, fields: vec![child(0, 4, "glue_x")] },
        ],
    };
    assert_eq!(run(&shape, 8, None), vec![call("glue_x", 4)]);
}

#[test]
fn an_array_glue_delegates_to_its_slice_glue_with_the_length() {
    let shape = GlueShape::ArrayDelegate { slice_glue: "glue_slice".to_string(), len: 5 };
    assert_eq!(run(&shape, 20, None), vec![("glue_slice".to_string(), 0, Some(5))]);
}

#[test]
fn a_slice_glue_drops_every_element_in_ascending_order() {
    let shape = GlueShape::ElementLoop { elem_glue: "glue_e".to_string(), stride: 12 };
    let calls = run_synthesized(
        "glue",
        &shape,
        &GlueRun { size: 36, align: 8, tag: None, elements: Some(3) },
    )
    .unwrap_or_else(|why| panic!("{why}"));
    assert_eq!(calls, vec![call("glue_e", 0), call("glue_e", 12), call("glue_e", 24)]);
    let none = run_synthesized(
        "glue",
        &shape,
        &GlueRun { size: 1, align: 8, tag: None, elements: Some(0) },
    )
    .unwrap_or_else(|why| panic!("{why}"));
    assert!(none.is_empty(), "an empty slice drops nothing: {none:?}");
}

/// A module holding one bodyless declaration per callee and the glue, as the lane builds it.
fn module_with(shape: &GlueShape<String>, fat: Option<Ty>) -> (Module, FuncId) {
    let mut module = Module::new("m");
    module.target_info = Some(crate::drop_glue_oracle::oracle_target());
    let ptr_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut names = Vec::new();
    for callee in shape.callees() {
        if !names.contains(callee) {
            names.push(callee.clone());
        }
    }
    let sig = match (&fat, shape.passes_fat_pointer()) {
        (Some(fat), true) => module
            .add_func_type(FuncTy {
                params: vec![fat.clone()],
                returns: vec![],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture"),
        _ => ptr_sig,
    };
    for (i, name) in names.iter().enumerate() {
        let mut f = Function::new(FuncId::new(i as u32), name.clone(), sig, BlockId::new(0));
        f.linkage = trust_ir::Linkage::External;
        module.try_add_function(f).expect("Module::try_add_function: test fixture");
    }
    let shape = shape
        .try_map(|n| {
            Ok::<FuncId, ()>(FuncId::new(names.iter().position(|m| m == n).unwrap() as u32))
        })
        .unwrap();
    let id = FuncId::new(names.len() as u32);
    let ty = module
        .add_func_type(glue_signature(&shape, fat.as_ref()).unwrap())
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(synthesize_glue(id, "glue", ty, &shape, fat.as_ref()).unwrap())
        .expect("Module::try_add_function: test fixture");
    (module, id)
}

#[test]
fn every_synthesized_shape_is_a_valid_trust_ir_function() {
    let mut fat_module = Module::new("rows");
    let row = fat_module.add_type(Ty::I8).expect("Module::add_type: test fixture");
    let fat = Ty::FatPtr(trust_ir::FatPtrKind::Slice(row));
    for (shape, fat) in [
        (GlueShape::Noop, None),
        (GlueShape::Fields { dtor: Some("d".to_string()), fields: vec![child(0, 4, "c")] }, None),
        (direct_enum(), None),
        (niche_enum(254), None),
        (GlueShape::ArrayDelegate { slice_glue: "s".to_string(), len: 2 }, Some(fat.clone())),
        (GlueShape::ElementLoop { elem_glue: "e".to_string(), stride: 4 }, Some(fat.clone())),
    ] {
        let (mut module, _) = module_with(&shape, fat);
        module.types = fat_module.types.clone();
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{shape:?}: {errors:?}");
    }
}

/// Every type a function's body or block parameters spell.
fn body_tys(f: &Function) -> Vec<Ty> {
    let mut out = Vec::new();
    for b in &f.blocks {
        out.extend(b.params.iter().map(|(_, t)| t.clone()));
        for n in &b.body {
            match &n.inst {
                Inst::Const { ty, .. } | Inst::Load { ty, .. } | Inst::Store { ty, .. } => {
                    out.push(ty.clone())
                }
                Inst::BinOp { ty, .. } | Inst::ICmp { ty, .. } => out.push(ty.clone()),
                Inst::GEP { pointee_ty, .. } => out.push(pointee_ty.clone()),
                Inst::PtrFromParts { ptr_ty, metadata_ty, .. }
                | Inst::PtrMetadata { ptr_ty, metadata_ty, .. } => {
                    out.push(ptr_ty.clone());
                    out.push(metadata_ty.clone());
                }
                Inst::PtrData { ptr_ty, .. } => out.push(ptr_ty.clone()),
                _ => {}
            }
        }
    }
    out
}

#[test]
fn a_thin_pointer_glue_body_names_no_table_row() {
    for shape in [
        GlueShape::Fields { dtor: Some("d".to_string()), fields: vec![child(0, 4, "c")] },
        direct_enum(),
        niche_enum(3),
    ] {
        let (module, id) = module_with(&shape, None);
        let f = module.function_by_id(id).unwrap();
        for t in body_tys(f) {
            assert!(
                matches!(
                    t,
                    Ty::Ptr | Ty::I8 | Ty::I64 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128
                ),
                "{shape:?} spells {t:?}"
            );
        }
        assert!(module.structs.is_empty() && module.enums.is_empty() && module.types.is_empty());
        assert_eq!(
            f.body_gate,
            Some(trust_ir::BodyGate::Gated {
                authority: TRUST_DROP_GLUE_AUTHORITY.to_string(),
                evidence: None
            })
        );
    }
}

fn drop_body() -> Function {
    let mut f = Function::new(FuncId::new(0), "f", trust_ir::FuncTyId::new(0), BlockId::new(0));
    let mut b0 = trust_ir::Block::new(BlockId::new(0));
    b0.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::U32, count: None, align: None })
            .with_result(ValueId::new(1)),
    );
    b0.body.push(InstrNode::new(Inst::Drop { ty: Ty::U32, ptr: ValueId::new(1) }));
    b0.body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![] }));
    let mut b1 = trust_ir::Block::new(BlockId::new(1));
    b1.body.push(InstrNode::new(Inst::Drop { ty: Ty::U64, ptr: ValueId::new(1) }));
    b1.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks = vec![b0, b1];
    f
}

#[test]
fn the_rewrite_turns_every_drop_into_a_call_of_its_resolved_glue() {
    let mut f = drop_body();
    let n = rewrite_drops(&mut f, |node| {
        Ok(if node.ty == Ty::U32 { FuncId::new(7) } else { FuncId::new(8) })
    })
    .unwrap();
    assert_eq!(n, 2);
    assert!(drop_nodes(&f).is_empty());
    assert_eq!(
        f.blocks[0].body[1].inst,
        Inst::Call { callee: FuncId::new(7), args: vec![ValueId::new(1)] }
    );
    assert_eq!(
        f.blocks[1].body[0].inst,
        Inst::Call { callee: FuncId::new(8), args: vec![ValueId::new(1)] }
    );
}

#[test]
fn the_rewrite_is_all_or_nothing() {
    let mut f = drop_body();
    let before = f.clone();
    let err = rewrite_drops(&mut f, |node| {
        if node.ty == Ty::U64 { Err("no glue".to_string()) } else { Ok(FuncId::new(7)) }
    });
    assert_eq!(err, Err("no glue".to_string()));
    assert_eq!(f, before, "a failed rewrite leaves the function untouched");
}

#[test]
fn the_postcondition_finds_a_drop_in_any_function() {
    let mut module = Module::new("m");
    let mut clean = drop_body();
    rewrite_drops(&mut clean, |_| Ok(FuncId::new(5))).unwrap();
    module.functions.push(clean);
    assert_eq!(first_surviving_drop(&module), None);
    let mut dirty = drop_body();
    dirty.id = FuncId::new(1);
    module.functions.push(dirty);
    assert_eq!(first_surviving_drop(&module), Some((FuncId::new(1), BlockId::new(0), 1)));
}
