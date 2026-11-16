//! Genuine TyCtxt identities and guards; no layout_of or source/lowering proof.
#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_mir_extract;

use rustc_middle::ty;
#[derive(Default)]
struct Observer {
    mismatches: usize,
}
impl rustc_driver::Callbacks for Observer {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let candidate = std::env::var_os("TRUST_LAYOUT_SUMMARY_CANDIDATE").is_some();
        let mut count = 0;
        for local in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(local) == rustc_hir::def::DefKind::AssocTy
                && matches!(
                    tcx.def_kind(tcx.parent(local.to_def_id())),
                    rustc_hir::def::DefKind::Impl { .. }
                )
            {
                let raw_rhs = tcx.type_of(local).instantiate_identity().skip_normalization();
                if let ty::Array(_, len) = raw_rhs.kind() {
                    println!(
                        "written array RHS owner={} constant_kind={:?}",
                        tcx.def_path_str(local),
                        len.kind()
                    );
                }
            }
        }
        for owner in tcx.hir_body_owners() {
            let Some(name) = tcx.opt_item_name(owner.to_def_id()) else { continue };
            let name = name.as_str();
            if !name.starts_with("case_") {
                continue;
            }
            let signature =
                tcx.fn_sig(owner).instantiate_identity().skip_normalization().skip_binder();
            assert_eq!(signature.inputs().len(), 1, "fixture interface");
            let raw = signature.inputs()[0];
            // This one intentionally retains its escaping source binder.
            let input = if name == "case_bound" {
                raw
            } else {
                let ty::Ref(_, pointee, _) = raw.kind() else { panic!("borrowed fixture root") };
                *pointee
            };
            if name == "case_supported_const" {
                let ty::Adt(def, args) = input.kind() else { unreachable!() };
                for field in def.all_fields() {
                    let field_ty =
                        tcx.type_of(field.did).instantiate(tcx, args).skip_normalization();
                    if let ty::Adt(_, args) = field_ty.kind() {
                        for constant in args.consts() {
                            println!(
                                "supported_const written field={} constant_kind={:?}",
                                field.name,
                                constant.kind()
                            );
                        }
                    }
                }
            }
            let (baseline, optimized, contextual, visits) = {
                let _freeze = trust_mir_extract::ctfe_reentrancy::enter_building(owner);
                assert!(trust_mir_extract::ctfe_reentrancy::frozen());
                let mut visits = 0;
                let baseline =
                    trust_mir_extract::ctfe_reentrancy::every_reached_type(tcx, input, &mut |t| {
                        visits += 1;
                        trust_mir_extract::ctfe_reentrancy::layout_query_is_reentrant_safe(t)
                    });
                let optimized =
                    trust_mir_extract::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(
                        tcx, input,
                    );
                let context =
                    trust_mir_extract::ctfe_reentrancy::LayoutQuerySafetyContext::new(tcx);
                let contextual = context.is_safe(input);
                (baseline, optimized, contextual, visits)
            };
            assert!(!trust_mir_extract::ctfe_reentrancy::frozen(), "freeze leaked");
            println!(
                "{name}: baseline={baseline} summary={optimized} context={contextual} baseline_visits={visits}"
            );
            let wanted_baseline = matches!(
                name,
                "case_short"
                    | "case_hrtb"
                    | "case_cap_safe"
                    | "case_literal_length_input"
                    | "case_named_length_input"
            );
            let projection_candidate =
                std::env::var_os("TRUST_LAYOUT_PROJECTION_CANDIDATE").is_some();
            let supported_candidate =
                std::env::var_os("TRUST_LAYOUT_SUPPORTED_PROJECTION_CANDIDATE").is_some();
            let confirmed_candidate =
                std::env::var_os("TRUST_LAYOUT_CONFIRMED_PROJECTION_CANDIDATE").is_some();
            let written_candidate =
                std::env::var_os("TRUST_LAYOUT_WRITTEN_PROJECTION_CANDIDATE").is_some();
            let foreign_candidate =
                std::env::var_os("TRUST_LAYOUT_FOREIGN_PREPARATION_CANDIDATE").is_some();
            let concrete_const_candidate =
                std::env::var_os("TRUST_LAYOUT_CONCRETE_CONST_CANDIDATE").is_some();
            let wanted_summary = (concrete_const_candidate && name == "case_supported_const")
                || (foreign_candidate
                    && matches!(name, "case_foreign_copy_projection" | "case_nonnull_projection"))
                || (confirmed_candidate
                    && matches!(name, "case_supported_recursive" | "case_supported_plain"))
                || (written_candidate && name == "case_literal_length_projection")
                || (supported_candidate
                    && matches!(
                        name,
                        "case_supported_recursive"
                            | "case_supported_plain"
                            | "case_supported_const"
                    ))
                || wanted_baseline
                || (candidate && name == "case_closed_reuse")
                || (projection_candidate
                    && matches!(
                        name,
                        "case_projection_reuse"
                            | "case_phantom_plain_projection"
                            | "case_value_const_projection"
                    ));
            if baseline != wanted_baseline
                || optimized != wanted_summary
                || contextual != wanted_summary
            {
                self.mismatches += 1;
                eprintln!(
                    "MISMATCH {name}: expected baseline={wanted_baseline} summary={wanted_summary}"
                );
            }
            count += 1;
        }
        assert_eq!(count, 47, "nonvacuous complete fixture population");
        println!(
            "layout summary native cases={count}; candidate={candidate}; mismatches={}",
            self.mismatches
        );
        // Let Rust finish checking the ordinary fixture. The freeze is gone;
        // no ill-typed source is blessed by stopping before analysis.
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("capture early") };
    let mut observer = Observer::default();
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut observer);
    assert_eq!(observer.mismatches, 0, "native guard mismatches after ordinary Rust analysis");
}
