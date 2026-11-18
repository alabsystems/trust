//! Actual producer converter/table controls, not S runtime admission.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_thir_lower;

use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, CRATE_DEF_INDEX};
use trust_thir_lower::concrete_type_transport::lower;

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
            // An actual source fn-pointer now has a complete type-table image. This
            // carries no callable body, physical ABI record, admission or proof token.
            let signature = tcx.fn_sig(named(tcx, "bad_callable")).instantiate_identity().skip_normalization();
            let callable_source = tcx.instantiate_bound_regions_with_erased(signature).inputs()[0];
            let callable = lower(tcx, instance, &[callable_source]).expect("actual fn(u8)->u8 type image");
            assert_eq!(callable.sources(), &[callable_source]);
            let [trust_ir::Ty::Func(callable_id)] = callable.roots() else {
                panic!("actual function pointer lost its checked signature");
            };
            let expected_callable = trust_ir::FuncTy {
                params: vec![trust_ir::Ty::U8], returns: vec![trust_ir::Ty::U8],
                is_vararg: false, abi: None,
            };
            assert_eq!(callable.module().func_type(*callable_id), Some(&expected_callable));
            assert!(callable.module().functions.is_empty() && callable.module().globals.is_empty()
                && callable.module().blobs.is_empty() && callable.module().proof_obligations.is_empty()
                && callable.module().proof_certificates.is_empty()
                && callable.module().obligation_diagnostics.is_empty()
                && callable.module().spec_modules.is_empty());
            let mut refusals = Vec::new();
            for name in ["bad_union", "bad_fat"] {
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
            rows.push(serde_json::json!({"actual_type":format!("{}",instance.args[1].as_type().unwrap()),"roots":image.roots().len(),"struct_rows":image.module().structs.len(),"array_tuple_rows":image.module().types.len(),"tuple_layouts":image.module().tuple_layouts.len(),"actual_concrete_producer_tables_equal":true,"actual_callable_type_image":true,"owner_is_local":owner.is_local(),"official_S_admission":false,"refusals":refusals}));
        }
        println!("{}", serde_json::to_string_pretty(&rows).unwrap());
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    let mut args: Vec<_> = std::env::args().collect(); args.push("-Zno-steal-thir".into());
    rustc_driver::run_compiler(&args, &mut Probe);
}
