#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate trust_mir_extract;
extern crate trust_thir_lower;

struct Observe;
impl rustc_driver::Callbacks for Observe {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let mut count = 0;
        for owner in tcx.hir_body_owners() {
            let path = tcx.def_path_str(owner);
            let name = path.rsplit("::").next().unwrap();
            if !name.starts_with("case_") {
                continue;
            }
            let (thir, root) = tcx.thir_body(owner).unwrap();
            let thir = thir.borrow();
            let _freeze = trust_thir_lower::enter_mir_built_ctfe_freeze(owner);
            let (lowered, drop_refusal) =
                trust_thir_lower::lower_module_from_thir_for_query(tcx, owner, &thir, root);
            let errors = trust_ir_build::validate_module(&lowered.module);
            let mut violations = Vec::new();
            lowered.module.visit_storage_violations(&lowered.module.layout_table(), |v| {
                violations.push(v);
            });
            eprintln!(
                "{name}: unsupported={:?} drop={drop_refusal:?} errors={errors:?} storage={violations:?}",
                lowered.unsupported
            );
            match name {
                "case_head" | "case_tail" | "case_read_tail" => {
                    assert!(lowered.unsupported.is_empty());
                    assert!(drop_refusal.is_none());
                    assert!(errors.is_empty());
                    assert!(violations.is_empty());
                    let parent = lowered.module.structs.iter().find(|s| s.name.ends_with("Parent"))
                        .expect("actual source parent retained");
                    assert_eq!((parent.size, parent.align), (Some(32), Some(8)));
                    assert_eq!(parent.fields.len(), 3);
                    assert_eq!(parent.fields[1].offset, Some(8));
                    assert_eq!(parent.fields[2].offset, Some(24));
                    assert_eq!(parent.fields[1].ty,
                        trust_ir::Ty::Storage(trust_ir::StorageLayout::new(16, 8)));
                }
                "case_enum_tail" => {
                    assert!(lowered.unsupported.is_empty());
                    assert!(drop_refusal.is_none());
                    assert!(errors.is_empty());
                    assert!(violations.is_empty());
                    let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
                    let rustc_middle::ty::Ref(_, source, _) = signature.inputs()[0].kind()
                        else { panic!("actual original reference input") };
                    let context = trust_mir_extract::ctfe_reentrancy::LayoutQuerySafetyContext::new(tcx);
                    assert!(context.is_safe(*source));
                    let actual = tcx.layout_of(rustc_middle::ty::TypingEnv::fully_monomorphized()
                        .as_query_input(*source)).expect("guarded source layout");
                    let parent = lowered.module.structs.iter().find(|s| s.name.ends_with("EnumParent"))
                        .expect("actual source enum parent retained");
                    assert_eq!((parent.size, parent.align),
                        (Some(actual.size.bytes()), Some(actual.align.bytes())));
                    for (index, field) in parent.fields.iter().enumerate() {
                        assert_eq!(field.offset, Some(actual.fields.offset(index).bytes()));
                    }
                    let mut storage = false;
                    lowered.module.visit_types(|ty| storage |= matches!(ty, trust_ir::Ty::Storage(_)));
                    assert!(storage, "actual storage survives the enclosing enum declaration");
                }
                "case_value_identity" | "case_parent_identity" | "case_enum_identity" => {
                    assert!(!violations.is_empty(), "whole-value storage is never licensed");
                    assert!(!errors.is_empty(), "ordinary validator enforces the same policy");
                }
                "case_lookalike" if std::env::var_os("TRUST_GENERIC_UNION_STORAGE_CONFIRMED")
                    .as_deref() == Some(std::ffi::OsStr::new("1")) => {
                    assert!(lowered.unsupported.is_empty() && errors.is_empty() && violations.is_empty());
                    assert!(drop_refusal.is_none() && !lowered.opaque_collapse);
                    let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
                    let rustc_middle::ty::Ref(_, parent_source, _) = signature.inputs()[0].kind()
                        else { panic!("actual parent reference") };
                    let rustc_middle::ty::Adt(parent, args) = parent_source.kind()
                        else { panic!("actual parent declaration") };
                    let source = parent.non_enum_variant().fields.iter().nth(1).unwrap()
                        .ty(tcx, *args).skip_normalization();
                    let context = trust_mir_extract::ctfe_reentrancy::LayoutQuerySafetyContext::new(tcx);
                    let geometry = context.union_storage(source).expect("separate actual union geometry");
                    assert_eq!(geometry.source(), source);
                    assert!(context.maybe_uninit_storage(source).is_none(), "not the lang item/payload witness");
                    assert_eq!((geometry.size_bytes(), geometry.align_bytes()), (16, 8));
                    let parent = lowered.module.structs.iter().find(|s| s.name.ends_with("LookalikeParent")).unwrap();
                    assert_eq!(parent.fields[1].ty, trust_ir::Ty::Storage(trust_ir::StorageLayout::new(16, 8)));
                    assert_eq!(parent.fields[2].offset, Some(24));
                }
                "case_lookalike" => {
                    let mut storage = false;
                    lowered.module.visit_types(|ty| storage |= matches!(ty, trust_ir::Ty::Storage(_)));
                    assert!(!storage, "matching union geometry is not source identity");
                    assert!(!lowered.unsupported.is_empty() || !errors.is_empty()
                        || drop_refusal.is_some() || lowered.opaque_collapse);
                }
                _ => panic!("unclassified source fixture {name}"),
            }
            count += 1;
        }
        assert_eq!(count, 8);
        eprintln!("STORAGE ADDRESS8 PASS; ordinary source analysis continues");
        rustc_driver::Compilation::Continue
    }
}

fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("early jobserver") };
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observe);
}
