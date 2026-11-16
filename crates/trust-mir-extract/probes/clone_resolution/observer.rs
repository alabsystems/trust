#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_mir_extract;
use rustc_middle::ty::{self, TyCtxt};
use trust_mir_extract::ctfe_reentrancy as cr;
struct Observe;
impl rustc_driver::Callbacks for Observe {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let clone_trait = tcx.lang_items().clone_trait().expect("real core Clone language item");
        let clone_method = tcx
            .associated_items(clone_trait)
            .in_definition_order()
            .find(|a| a.name().as_str() == "clone")
            .expect("actual Clone method")
            .def_id;
        let confirmed = std::env::var_os("TRUST_ADT_CLONE_CONFIRMED").is_some();
        let mut count = 0;
        for owner in tcx.hir_body_owners() {
            if tcx.def_kind(owner) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            let name = tcx.item_name(owner.to_def_id());
            let name = name.as_str();
            if !name.starts_with("case_") {
                continue;
            }
            let sig = tcx.fn_sig(owner).instantiate_identity().skip_norm_wip().skip_binder();
            let ty::Ref(_, actual, _) = sig.inputs()[0].kind() else {
                panic!("actual reference input")
            };
            let args = tcx.mk_args(&[(*actual).into()]);
            let _freeze = cr::enter_building(owner);
            let allowed =
                cr::resolution_reveal_free(tcx, ty::ParamEnv::empty(), clone_method, args);
            let expected = match name {
                "case_adt" => confirmed,
                "case_opaque_bound" | "case_nonleaf_bound" | "case_tuple" | "case_fnptr"
                | "case_opaque" | "case_generic" | "case_many_bounds" => false,
                _ => panic!("unclassified source case"),
            };
            eprintln!("{name}: actual={actual:?} query_allowed={allowed} expected={expected}");
            assert_eq!(allowed, expected, "exact guarded Clone query capability");
            if allowed {
                let instance = ty::Instance::try_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    clone_method,
                    args,
                )
                .expect("actual compiler selection")
                .expect("concrete generated ADT impl");
                assert!(matches!(instance.def, ty::InstanceKind::Item(_)));
                assert_ne!(instance.def_id(), clone_method);
                eprintln!("ACTUAL INSTANCE {instance:?}; no body or execution authority");
            }
            count += 1;
        }
        assert_eq!(count, 8);
        eprintln!("CLONE QUERY8 PASS; ordinary Rust analysis continues");
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observe);
}
