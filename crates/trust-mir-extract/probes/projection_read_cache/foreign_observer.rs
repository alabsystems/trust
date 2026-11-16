#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_mir_extract;

use rustc_middle::ty::{self, TyCtxt};
use trust_mir_extract::ctfe_reentrancy::{self, LayoutQuerySafetyContext};

struct Observe;
impl rustc_driver::Callbacks for Observe {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let candidate = std::env::var_os("TRUST_COMPLETED_READER_CONFIRMED").is_some();
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
            let _freeze = ctfe_reentrancy::enter_building(owner);
            let signature = tcx.fn_sig(owner).instantiate_identity().skip_norm_wip().skip_binder();
            assert_eq!(signature.inputs().len(), 3);
            let ty::Ref(_, leaf, _) = signature.inputs()[0].kind() else {
                panic!("source leaf reference")
            };
            let ty::Ref(_, prime, _) = signature.inputs()[1].kind() else {
                panic!("original prime reference")
            };
            let ty::Ref(_, reached, _) = signature.inputs()[2].kind() else {
                panic!("original reached reference")
            };
            let context = LayoutQuerySafetyContext::new(tcx);
            assert!(context.is_safe(*leaf), "independent original Leaf guard");
            assert!(context.is_safe(*prime), "independent original Expr guard");
            let result = context.is_safe(*reached);
            let expected = match name {
                "case_foreign_repeat" => candidate,
                "case_foreign_unsafe" => false,
                _ => panic!("unclassified source case"),
            };
            eprintln!("{name}: reached={reached:?} result={result} expected={expected}");
            assert_eq!(result, expected, "exact foreign source cache control");
            count += 1;
        }
        assert_eq!(count, 2, "nonvacuous foreign source population");
        eprintln!("FOREIGN PROJECTION READ2 PASS; ordinary Rust analysis continues");
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observe);
}
