//! Actual converter/table placement plus synthetic S data construction.
//! Real TCX and metadata; the deliberately assembled template has no source/body authority.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate trust_thir_lower;

use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, CRATE_DEF_INDEX};
use trust_thir_lower::concrete_type_transport::lower;
use trust_ir::{Block, BlockId, BodyGate, FieldDef, FuncId, FuncTy, Function, HoleId, Inst, InstG, InstrNode, InstrNodeG, Module, ParamId, Producer, StructDef, StructId, StructRepr, TemplateRef, Ty, TyG, ValueId};
use trust_ir::template::{HoleDef, HoleKind, TemplateArg, TypeContract};
use trust_thir_lower::template_metadata::{self as codec, instantiate::{self, TemplateProvider}};

fn place_actual(image: &trust_thir_lower::concrete_type_transport::ConcreteTypes<'_>) -> usize {
    let mut host = Module::new("prior-owned-context");
    host.target_info = image.module().target_info.clone();
    host.types.push(Ty::U64);
    host.structs.push(StructDef { id: StructId::new(0), name: image.module().structs[0].name.clone(),
        fields: vec![FieldDef { name: "different_actual_row".into(), ty: Ty::U64, offset: Some(0) }],
        size: Some(8), align: Some(8), repr: StructRepr::C, origin: None });
    let original = host.clone();
    let placed = codec::type_host::merge(&host, image).unwrap();
    assert_eq!(host, original, "read-only host/image API");
    assert_eq!(placed.module().types[0], Ty::U64);
    assert_eq!(placed.module().structs[0], original.structs[0]);
    assert!(placed.module().structs.len() > image.module().structs.len(), "same name is no identity");
    assert!(trust_ir_build::validate::validate_module(placed.module()).is_empty());
    assert!(placed.module().functions.is_empty() && placed.module().proof_obligations.is_empty());
    let repeated = codec::type_host::merge(placed.module(), image).unwrap();
    // The canonical merger may append equivalent carrier/type rows; it
    // preserves nominal reuse and exact mapped roots rather than compacting.
    assert_eq!(repeated.module().structs, placed.module().structs);
    assert_eq!(repeated.module().enums, placed.module().enums);
    assert_eq!(repeated.module().tuple_layouts, placed.module().tuple_layouts);
    assert!(trust_ir_build::validate::validate_module(repeated.module()).is_empty());
    assert_eq!(repeated.roots(), placed.roots());
    placed.roots().len()
}

struct DataProvider { bytes: Vec<u8> }
impl<'tcx> TemplateProvider<'tcx> for DataProvider {
    fn load(&mut self, tcx: TyCtxt<'tcx>, owner: DefId) -> Result<codec::AuthenticatedTemplate, codec::MetadataError> {
        codec::read(&self.bytes, &codec::rustc::owner_bindings(tcx, owner)?, tcx.sess.overflow_checks())
    }
}

// Deliberately assembled data fixture. Expected owner/slots, actual Instance,
// keys and layout come from TCX; these bytes do NOT claim source refinement.
fn constructed_data<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> serde_json::Value {
    let owner = instance.def_id();
    let adt = named(tcx, "HostPair");
    let key = trust_thir_lower::template_key::encode(&trust_thir_lower::template_key::HoleKey::Type(
        trust_thir_lower::template_key::KeyTy::Adt(trust_thir_lower::template_key::rustc::stable_def(tcx, adt),
            vec![trust_thir_lower::template_key::KeyArg::Type(trust_thir_lower::template_key::KeyTy::Param(1))]),
    )).unwrap();
    let image = trust_thir_lower::concrete_type_transport::from_key(tcx, instance, &key).unwrap();
    let physical = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(image.sources()[0])).unwrap();
    let Ty::Struct(id) = image.roots()[0] else { panic!("actual HostPair is not a struct") };
    let sd = &image.module().structs[id.as_usize()];
    assert_eq!(sd.size, Some(physical.size.bytes()));
    assert_eq!(sd.align, Some(physical.align.bytes()));
    assert_eq!(sd.fields.iter().map(|f| f.offset.unwrap()).collect::<Vec<_>>(),
        (0..2).map(|i| physical.fields.offset(i).bytes()).collect::<Vec<_>>());
    place_actual(&image);
    let bindings = codec::rustc::owner_bindings(tcx, owner).unwrap();
    assert_eq!(bindings.slots.len(), 3, "lifetime/type/const original slots");
    let mut module = Module::new("synthetic-type-hole-data-only");
    module.target_info = image.module().target_info.clone();
    let ft = module.intern_func_type(FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None }).unwrap();
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    let mut f = Function::new(FuncId::new(0), "synthetic-type-hole", ft, BlockId::new(0)).with_producer(Producer::TRust);
    f.blocks = vec![block]; module.try_add_function(f).unwrap();
    let facts = trust_thir_lower::template_lowering::LaneFacts { owner: Some(bindings.owner),
        parameter_indices: vec![1,2], params: vec![trust_thir_lower::template_lowering::LaneParam::Type,
            trust_thir_lower::template_lowering::LaneParam::Const(Ty::Usize)], ..Default::default() };
    let mut template = trust_thir_lower::template_lowering::abstract_template(&module, &facts, "synthetic::type-hole-data".into()).unwrap();
    let param = TyG::Ext(TemplateRef::Param(ParamId::new(0)));
    template.header.holes.push(HoleDef { kind: HoleKind::Type { contract: TypeContract::Struct { fields: vec![param.clone(), TyG::U64] } },
        key, args: vec![TemplateArg::Type(param.clone())] });
    template.module.functions[0].blocks[0].body.insert(0, InstrNodeG::new(InstG::Alloca {
        ty: TyG::Ext(TemplateRef::Hole(HoleId::new(0))), count: None, align: None,
    }).with_result(ValueId::new(1)));
    template.module.functions[0].blocks[0].body.insert(1, InstrNodeG::new(InstG::Drop {
        ty: TyG::Ext(TemplateRef::Hole(HoleId::new(0))), ptr: ValueId::new(1),
    }));
    let evidence = trust_thir_lower::rmeta_entry::encode_evidence(&trust_thir_lower::rmeta_entry::Evidence {
        arg_count: 1, arg_enum: vec![false], ..Default::default() });
    let bytes = codec::frame(&bindings, &template, tcx.sess.overflow_checks(), &evidence).unwrap();
    let good = instantiate::construct_with(tcx, instance, &mut DataProvider { bytes }).unwrap();
    let result = good.module();
    assert!(trust_ir_build::validate::validate_module(result).is_empty());
    assert!(result.functions.iter().all(|f| f.body_gate == Some(BodyGate::Ungated)));
    assert!(result.proof_obligations.is_empty() && result.proof_certificates.is_empty());
    assert!(!result.functions[0].blocks[0].body.iter().any(|n| matches!(n.inst, Inst::Drop { .. })), "actual NoDestructor erased only the requested drop");
    let Inst::Alloca { ty: Ty::Struct(installed), .. } = result.functions[0].blocks[0].body[0].inst else { panic!("hole did not reference an installed nominal row") };
    assert_eq!(result.structs[installed.as_usize()].fields, sd.fields);
    assert_eq!(result.structs[installed.as_usize()].size, sd.size);
    assert_eq!(result.structs[installed.as_usize()].align, sd.align);
    let good_digest = result.stable_digest();
    let mut refusals = Vec::new();
    template.header.holes[0].kind = HoleKind::Type { contract: TypeContract::Struct { fields: vec![TyG::U64, param.clone()] } };
    let bad_bytes = codec::frame(&bindings, &template, tcx.sess.overflow_checks(), &evidence).unwrap();
    let reason = match instantiate::construct_with(tcx, instance, &mut DataProvider { bytes: bad_bytes }) {
        Err(e) => e.0, Ok(_) => panic!("reordered field contract accepted") };
    assert!(reason.contains("contract says"), "{reason}");
    refusals.push(serde_json::json!({"case":"logical-field-contract-reordered","reason":reason}));
    template.header.holes[0].kind = HoleKind::Type { contract: TypeContract::Opaque };
    let glue = named(tcx, "NeedsGlue");
    template.header.holes[0].key = trust_thir_lower::template_key::encode(&trust_thir_lower::template_key::HoleKey::Type(
        trust_thir_lower::template_key::KeyTy::Adt(trust_thir_lower::template_key::rustc::stable_def(tcx, glue), vec![trust_thir_lower::template_key::KeyArg::Type(trust_thir_lower::template_key::KeyTy::Param(1))]),
    )).unwrap();
    let bad_bytes = codec::frame(&bindings, &template, tcx.sess.overflow_checks(), &evidence).unwrap();
    let reason = match instantiate::construct_with(tcx, instance, &mut DataProvider { bytes: bad_bytes }) {
        Err(e) => e.0, Ok(_) => panic!("real nontrivial destructor accepted without glue body") };
    assert!(reason.contains("requires actual glue body linkage"), "{reason}");
    refusals.push(serde_json::json!({"case":"actual-needs-drop-without-glue","reason":reason}));
    if matches!(instance.args[1].as_type().unwrap().kind(), ty::RawPtr(..)) {
        template.header.holes[0].key = trust_thir_lower::template_key::encode(&trust_thir_lower::template_key::HoleKey::Type(
            trust_thir_lower::template_key::KeyTy::RawPtr { mutable: false,
                pointee: Box::new(trust_thir_lower::template_key::KeyTy::Tuple(vec![trust_thir_lower::template_key::KeyTy::Param(1)])) },
        )).unwrap();
        let bad_bytes = codec::frame(&bindings, &template, tcx.sess.overflow_checks(), &evidence).unwrap();
        let reason = match instantiate::construct_with(tcx, instance, &mut DataProvider { bytes: bad_bytes }) {
            Err(e) => e.0, Ok(_) => panic!("distinct actual source types collapsed into Ptr") };
        assert!(reason.contains("distinct Rust source types collide"), "{reason}");
        refusals.push(serde_json::json!({"case":"real-pointer-source-identity-collision","reason":reason}));
    }
    assert_eq!(good.module().stable_digest(), good_digest, "failed construction does not alter retained data");
    serde_json::json!({"actual_type":format!("{}", instance.args[1].as_type().unwrap()), "owner_is_local":owner.is_local(),
        "actual_layout_matches":true,"constructed_type_hole_data":true,"ungated":true,"official_S_admission":false,"refusals":refusals})
}


fn named(tcx: TyCtxt<'_>, name: &str) -> DefId {
    let mut found: Vec<_> = tcx.hir_crate_items(()).definitions().map(|d| d.to_def_id())
        .filter(|&d| tcx.opt_item_name(d).is_some_and(|n| n.as_str() == name)).collect();
    if found.is_empty() {
        for &krate in tcx.crates(()) {
            if tcx.crate_name(krate).as_str() == "template_type_transport_source" {
                found.extend(tcx.module_children(DefId { krate, index: CRATE_DEF_INDEX }).iter()
                    .filter(|c| c.ident.name.as_str() == name).filter_map(|c| c.res.opt_def_id()));
            }
        }
    }
    assert_eq!(found.len(), 1, "actual source definition {name}"); found[0]
}

struct Probe;
impl rustc_driver::Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> rustc_driver::Compilation {
        let owner = named(tcx, "owner");
        let main = named(tcx, "main").as_local().unwrap();
        let (thir, _) = tcx.thir_body(main).unwrap();
        let thir = thir.borrow();
        let mut instances = Vec::new();
        for expr in &thir.exprs {
            if let rustc_middle::thir::ExprKind::Call { fun, .. } = expr.kind {
                if let ty::FnDef(def, args) = *thir.exprs[fun].ty.kind() {
                    if def == owner {
                        let args = tcx.erase_and_anonymize_regions(args.skip_binder());
                        instances.push(ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def, args).unwrap().unwrap());
                    }
                }
            }
        }
        drop(thir); assert_eq!(instances.len(), 2);
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_normalization();
        let types = tcx.instantiate_bound_regions_with_erased(signature).inputs().to_vec();
        let mut rows = Vec::new();
        for instance in instances {
            let image = lower(tcx, instance, &types).unwrap();
            let small = matches!(instance.args[1].as_type().unwrap().kind(), ty::Uint(ty::UintTy::U8));
            let concrete = named(tcx, if small { "concrete_u8" } else { "concrete_u16" }).as_local().unwrap();
            let (thir, root) = tcx.thir_body(concrete).unwrap();
            let thir = thir.borrow();
            let (oracle, _) = trust_thir_lower::lower_module_from_thir_for_query(tcx, concrete, &thir, root);
            assert!(oracle.unsupported.is_empty(), "actual concrete producer refused: {:?}", oracle.unsupported);
            let sig = &oracle.module.func_types[oracle.module.functions[0].ty.as_usize()];
            assert_eq!(image.roots(), sig.params, "actual concrete producer signature");
            assert_eq!(image.module().types, oracle.module.types, "actual type table");
            assert_eq!(image.module().structs, oracle.module.structs, "actual nominal fields/layouts including ZST");
            assert_eq!(image.module().enums, oracle.module.enums, "actual enum rows");
            assert_eq!(image.module().tuple_layouts, oracle.module.tuple_layouts, "actual tuple offsets");
            assert!(image.module().functions.is_empty() && image.module().proof_obligations.is_empty());
            let installed_roots = place_actual(&image);
            assert_eq!(image.module().structs.len(), 4, "PhantomData,Inner,Packet,Pair");
            // Resolve an actual owner-relative Packet<T> key and compare its
            // standalone table image against the same converter input term.
            let key = trust_thir_lower::template_key::HoleKey::Type(
                trust_thir_lower::template_key::rustc::checked_type_key(tcx, types[1], owner).unwrap(),
            );
            let key = trust_thir_lower::template_key::encode(&key).unwrap();
            let keyed = trust_thir_lower::concrete_type_transport::from_key(tcx, instance, &key).unwrap();
            let direct = lower(tcx, instance, &types[1..2]).unwrap();
            assert_eq!(keyed.roots(), direct.roots());
            assert_eq!(keyed.module().stable_digest(), direct.module().stable_digest(), "actual nominal key resolution");
            let mut refusals = Vec::new();
            for name in ["bad_union", "bad_fat", "bad_callable"] {
                let sig = tcx.fn_sig(named(tcx, name)).instantiate_identity().skip_normalization();
                let bad = tcx.instantiate_bound_regions_with_erased(sig).inputs()[0];
                let error = match lower(tcx, instance, &[bad]) { Ok(_) => panic!("hostile type {name} was accepted"), Err(e) => e };
                assert!(error.starts_with("concrete type transport"), "{name}: {error}");
                refusals.push(serde_json::json!({"case":name,"reason":error}));
            }
            let mut malformed = instance.args.iter().collect::<Vec<_>>();
            malformed[1] = tcx.lifetimes.re_erased.into();
            let malformed = ty::Instance { def: instance.def, args: tcx.mk_args(&malformed) };
            let error = match lower(tcx, malformed, &types) { Ok(_) => panic!("wrong argument kind accepted"), Err(e) => e };
            assert_eq!(error, "template key generic argument kind");
            refusals.push(serde_json::json!({"case":"wrong-positional-kind","reason":error}));
            for (index, expected) in [(0,"template key parameter is not a type"),(2,"template key parameter is not a type"),(99,"template key parameter index")] {
                let bad = trust_thir_lower::template_key::encode(&trust_thir_lower::template_key::HoleKey::Type(trust_thir_lower::template_key::KeyTy::Param(index))).unwrap();
                let error = match trust_thir_lower::concrete_type_transport::from_key(tcx, instance, &bad) { Ok(_) => panic!("wrong type parameter position accepted"), Err(e) => e };
                assert_eq!(error,expected);
                refusals.push(serde_json::json!({"case":format!("wrong-type-key-position-{index}"),"reason":error}));
            }
            let bad = trust_thir_lower::template_key::rustc::checked_call_key(tcx,owner,instance.args,owner).unwrap();
            let bad = trust_thir_lower::template_key::encode(&bad).unwrap();
            let error = match trust_thir_lower::concrete_type_transport::from_key(tcx, instance, &bad) { Ok(_) => panic!("callee key used as type key"), Err(e) => e };
            assert_eq!(error,"concrete type transport received a different hole-key kind");
            refusals.push(serde_json::json!({"case":"callee-key-as-type","reason":error}));
            let repeated = lower(tcx, instance, &types).unwrap();
            assert_eq!(image.module().stable_digest(), repeated.module().stable_digest(), "failed requests cannot alter a later type image");
            rows.push(serde_json::json!({"actual_type":format!("{}",instance.args[1].as_type().unwrap()),"roots":image.roots().len(),"struct_rows":image.module().structs.len(),"array_tuple_rows":image.module().types.len(),"tuple_layouts":image.module().tuple_layouts.len(),"actual_concrete_producer_tables_equal":true,"canonically_installed_roots":installed_roots,"owner_is_local":owner.is_local(),"official_S_admission":false,"refusals":refusals}));
        }
        let host_owner = named(tcx, "host_owner");
        let (thir, _) = tcx.thir_body(main).unwrap(); let thir = thir.borrow();
        let mut constructed = Vec::new();
        for expr in &thir.exprs {
            if let rustc_middle::thir::ExprKind::Call { fun, .. } = expr.kind {
                if let ty::FnDef(def, args) = *thir.exprs[fun].ty.kind() {
                    if def == host_owner {
                        let args = tcx.erase_and_anonymize_regions(args.skip_binder());
                        let instance = ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def, args).unwrap().unwrap();
                        constructed.push(constructed_data(tcx, instance));
                    }
                }
            }
        }
        assert_eq!(constructed.len(),3);
        println!("{}", serde_json::to_string_pretty(&serde_json::json!({"producer_images":rows,"constructed_data":constructed})).unwrap());
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    let mut args: Vec<_> = std::env::args().collect(); args.push("-Zno-steal-thir".into());
    rustc_driver::run_compiler(&args, &mut Probe);
}
