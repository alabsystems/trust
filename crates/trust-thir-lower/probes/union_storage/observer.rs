#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate trust_mir_extract;
extern crate trust_thir_lower;

use rustc_middle::ty::{self, TyCtxt};
struct Observe;
impl rustc_driver::Callbacks for Observe {
    fn after_expansion<'tcx>(
        &mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let mut count = 0;
        let mut generic_sources = Vec::new();
        let mut drop_sources = Vec::new();
        for owner in tcx.hir_body_owners() {
            let path = tcx.def_path_str(owner);
            let name = path.rsplit("::").next().unwrap();
            if !name.starts_with("case_") { continue; }
            let (thir, root) = tcx.thir_body(owner).unwrap();
            let thir = thir.borrow();
            let _freeze = trust_thir_lower::enter_mir_built_ctfe_freeze(owner);
            let context = trust_mir_extract::ctfe_reentrancy::LayoutQuerySafetyContext::new(tcx);
            let signature = tcx.fn_sig(owner).instantiate_identity().skip_norm_wip().skip_binder();
            let input = signature.inputs().first().copied();
            let source = input.map(|t| match t.kind() { ty::Ref(_, inner, _) => *inner, _ => t });
            match name {
                "case_struct_identity" | "case_enum_identity" => {
                    let source = source.unwrap();
                    assert!(context.union_storage(source).is_none(), "nominal union identity");
                    assert!(context.maybe_uninit_storage(source).is_none());
                }
                "case_generic_u64" | "case_generic_array" => {
                    let source = source.unwrap();
                    let geometry = context.union_storage(source).expect("actual generic union");
                    assert_eq!(geometry.source(), source);
                    assert!(context.maybe_uninit_storage(source).is_none(), "not a lang item token");
                    assert_eq!(geometry.align_bytes(), 8);
                    assert_eq!(geometry.size_bytes(), if name == "case_generic_u64" { 8 } else { 24 });
                    generic_sources.push(source);
                }
                "case_drop_a_identity" | "case_drop_b_identity" => {
                    let source = source.unwrap();
                    let ty::Adt(def, _) = source.kind() else { panic!("actual nominal union") };
                    assert!(def.is_union() && def.has_dtor(tcx));
                    let geometry = context.union_storage(source).expect("factual geometry does not grant drop");
                    assert_eq!(geometry.source(), source);
                    assert_eq!((geometry.size_bytes(), geometry.align_bytes()), (16, 8));
                    assert!(context.maybe_uninit_storage(source).is_none());
                    drop_sources.push(source);
                }
                _ => {}
            }
            let (lowered, drop_refusal) = trust_thir_lower::lower_module_from_thir_for_query(
                tcx, owner, &thir, root,
            );
            let errors = trust_ir_build::validate_module(&lowered.module);
            let mut violations = Vec::new();
            lowered.module.visit_storage_violations(&lowered.module.layout_table(), |v| violations.push(v));
            let mut has_storage = false;
            lowered.module.visit_types(|t| has_storage |= matches!(t, trust_ir::Ty::Storage(_)));
            eprintln!("{name}: unsupported={:?} drop={drop_refusal:?} opaque={} errors={errors:?} storage={violations:?}", lowered.unsupported, lowered.opaque_collapse);
            match name {
                "case_union_tail" | "case_union_read" => {
                    assert!(lowered.unsupported.is_empty() && errors.is_empty() && violations.is_empty());
                    assert!(drop_refusal.is_none() && !lowered.opaque_collapse);
                    let parent = lowered.module.structs.iter().find(|s| s.name.ends_with("Parent")).unwrap();
                    assert_eq!((parent.size, parent.align), (Some(32), Some(8)));
                    assert_eq!(parent.fields[1].offset, Some(8));
                    assert_eq!(parent.fields[2].offset, Some(24));
                    assert_eq!(parent.fields[1].ty, trust_ir::Ty::Storage(trust_ir::StorageLayout::new(16, 8)));
                }
                "case_union_identity" | "case_parent_identity" | "case_union_load"
                | "case_union_store" | "case_union_arg" | "case_union_result" => {
                    assert!(has_storage);
                    assert!(!errors.is_empty() && !violations.is_empty(), "shared whole-value/ABI floor");
                }
                "case_packed_read" => {
                    assert!(!lowered.unsupported.is_empty() || !errors.is_empty()
                        || drop_refusal.is_some(), "integer read through packed parent remains refused");
                }
                "case_drop_a_ref" | "case_drop_b_ref" | "case_drop_a_identity"
                | "case_drop_b_identity" | "case_drop_a_explicit" => {
                    assert!(!has_storage, "custom destructor keeps established confinement");
                    assert!(!lowered.unsupported.is_empty() || !errors.is_empty()
                        || drop_refusal.is_some() || lowered.opaque_collapse,
                        "no new nominal destructor or address authority");
                }
                "case_struct_identity" | "case_enum_identity" | "case_generic_u64"
                | "case_generic_array" => {}
                _ => panic!("unclassified source case"),
            }
            count += 1;
        }
        assert_eq!(generic_sources.len(), 2);
        assert_ne!(generic_sources[0], generic_sources[1]);
        assert_eq!(drop_sources.len(), 2);
        assert_ne!(drop_sources[0], drop_sources[1], "same layout is not destructor identity");
        assert_eq!(count, 18);
        eprintln!("UNION STORAGE18 PASS; ordinary source analysis continues");
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observe);
}
