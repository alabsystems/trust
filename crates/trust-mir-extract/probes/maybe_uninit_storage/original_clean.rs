#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_mir_extract;
use rustc_middle::ty::{self, TypeVisitableExt};
struct Capture;
impl rustc_driver::Callbacks for Capture {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let owner = tcx
            .hir_body_owners()
            .find(|d| tcx.def_path_str(*d).ends_with("MonadInst::uv"))
            .unwrap();
        let _freeze = trust_mir_extract::ctfe_reentrancy::enter_building(owner);
        let context = trust_mir_extract::ctfe_reentrancy::LayoutQuerySafetyContext::new(tcx);
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
        let ty::Ref(_, parent, _) = signature.inputs()[0].kind() else { panic!("actual ref") };
        let ty::Adt(def, args) = parent.kind() else { panic!("actual parent") };
        let level = def
            .non_enum_variant()
            .fields
            .iter()
            .next()
            .unwrap()
            .ty(tcx, *args)
            .skip_normalization();
        assert!(context.is_safe(level));
        assert!(context.maybe_uninit_storage(*parent).is_none());
        assert!(context.maybe_uninit_storage(level).is_none());
        let mut work = vec![*parent];
        let mut seen = Vec::new();
        let mut found = 0;
        while let Some(t) = work.pop() {
            if seen.contains(&t) {
                continue;
            }
            assert!(seen.len() < 1024, "bounded diagnostic inventory");
            seen.push(t);
            match t.kind() {
                ty::Adt(def, args) => {
                    if tcx.lang_items().maybe_uninit() == Some(def.did()) {
                        let result = context.maybe_uninit_storage(t);
                        eprintln!("ACTUAL SOURCE {t:?} witness={}", result.is_some());
                        if let Some(w) = result {
                            assert_eq!(w.source(), t);
                            assert_eq!(w.pointer_bits(), 64);
                            eprintln!(
                                "ACTUAL STORAGE payload={:?} size={} align={}",
                                w.payload(),
                                w.size_bytes(),
                                w.align_bytes()
                            );
                            if matches!(w.payload().kind(),ty::Array(elem,_) if *elem==level) {
                                assert_eq!((w.size_bytes(), w.align_bytes()), (80, 8));
                                found += 1;
                            }
                        }
                    }
                    if !t.has_opaque_types() && !t.has_non_region_param() {
                        for field in def.all_fields() {
                            work.push(field.ty(tcx, *args).skip_normalization());
                        }
                    }
                }
                ty::Ref(_, inner, _)
                | ty::RawPtr(inner, _)
                | ty::Slice(inner)
                | ty::Array(inner, _) => work.push(*inner),
                ty::Tuple(fields) => work.extend(fields.iter()),
                _ => {}
            }
        }
        assert_eq!(found, 1, "exact original MaybeUninit<[Level;2]> witness");
        eprintln!("ACTUAL ORIGINAL STORAGE CUSTODY PASS; no value/drop/ABI/provenance authority");
        rustc_driver::Compilation::Stop
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Capture)
}
