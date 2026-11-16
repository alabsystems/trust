#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_mir_extract;
use rustc_middle::ty::{self, TypeVisitableExt};
struct Observe;
impl rustc_driver::Callbacks for Observe {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let mut count = 0;
        for owner in tcx.hir_body_owners() {
            let name = tcx.def_path_str(owner).rsplit("::").next().unwrap().to_owned();
            if !name.starts_with("case_") {
                continue;
            }
            let _freeze = trust_mir_extract::ctfe_reentrancy::enter_building(owner);
            let context = trust_mir_extract::ctfe_reentrancy::LayoutQuerySafetyContext::new(tcx);
            let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
            let source = signature.inputs()[0];
            let expected = match name.as_str() {
                "case_scalar" => Some((8, 8)),
                "case_array" => Some((16, 8)),
                "case_unit" => Some((0, 1)),
                "case_empty_array" => Some((0, 8)),
                "case_aligned" => Some((32, 32)),
                "case_lookalike"
                | "case_wrapper"
                | "case_plain"
                | "case_pointer"
                | "case_generic"
                | "case_unrevealed_alias" => None,
                _ => panic!("unclassified fixture"),
            };
            if name == "case_generic" {
                assert!(source.has_non_region_param());
            }
            if name == "case_unrevealed_alias" {
                let ty::Adt(_, args) = source.kind() else {
                    panic!("actual MaybeUninit alias input")
                };
                assert!(
                    matches!(args.type_at(0).kind(), ty::Alias(..)),
                    "unrevealed original alias must not silently become its hidden value type"
                );
            }
            let result = context.maybe_uninit_storage(source);
            let observed = result.as_ref().map(|w| (w.size_bytes(), w.align_bytes()));
            eprintln!("{name}: expected={expected:?} observed={observed:?} source={source:?}");
            assert_eq!(observed, expected);
            if let Some(w) = result {
                assert_eq!(w.source(), source);
                assert_eq!(w.pointer_bits(), 64);
            }
            count += 1;
        }
        assert_eq!(count, 11);
        eprintln!("STORAGE WITNESS11 PASS; normal source analysis continues");
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observe);
}
