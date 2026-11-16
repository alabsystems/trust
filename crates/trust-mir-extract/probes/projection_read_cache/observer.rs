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
            let signature = tcx.fn_sig(owner).instantiate_identity().skip_norm_wip().skip_binder();
            let ty::Ref(_, source, _) = signature.inputs()[0].kind() else {
                panic!("source reference")
            };
            let _freeze = ctfe_reentrancy::enter_building(owner);
            let baseline = ctfe_reentrancy::every_reached_type(tcx, *source, &mut |t| {
                ctfe_reentrancy::layout_query_is_reentrant_safe(t)
            });
            let context = LayoutQuerySafetyContext::new(tcx);
            let result = context.is_safe(*source);
            eprintln!("{name}: baseline={baseline} completed_reader={result}");
            let expected = match name {
                "case_reuse" | "case_epoch_leaf" => true,
                "case_unsafe_sibling" | "case_wrong_args" | "case_nonleaf_rhs" | "case_growing" => {
                    false
                }
                _ => panic!("unclassified source case"),
            };
            assert!(!baseline, "the uncached original depth boundary must discriminate");
            assert_eq!(result, expected, "exact source cache control {name}");
            if name == "case_epoch_leaf" {
                let unnamed = ctfe_reentrancy::enter();
                assert!(!context.is_safe(*source), "unnamed frame revokes the cached leaf read");
                assert!(
                    !LayoutQuerySafetyContext::new(tcx).is_safe(*source),
                    "fresh policy also refuses CTFE"
                );
                drop(unnamed);
                assert!(
                    context.is_safe(*source),
                    "restored named policy reproves from empty facts"
                );
            }
            count += 1;
        }
        assert_eq!(count, 6, "nonvacuous ordinary-source population");
        eprintln!("PROJECTION READ CACHE6 PASS; ordinary Rust analysis continues");
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observe);
}
