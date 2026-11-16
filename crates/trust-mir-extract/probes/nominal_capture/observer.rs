//! Actual query -> owned shared faithful capture -> existing TrustIR consumer.
#![feature(rustc_private)]
extern crate rustc_attr_ir;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate trust_ir;
extern crate trust_ir_bridge;
extern crate trust_ir_build;
extern crate trust_mir_extract;
extern crate trust_types;
#[path = "../../src/nominal_body.rs"]
mod nominal_body;
#[path = "../../src/nominal_capture.rs"]
mod nominal_capture;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
pub use trust_mir_extract::{ctfe_reentrancy, extract_function_faithful};
struct Observer;
impl rustc_driver::Callbacks for Observer {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let owner = tcx
            .hir_body_owners()
            .find(|d| tcx.opt_item_name(d.to_def_id()).is_some_and(|n| n.as_str() == "original"))
            .unwrap();
        let snapshot = tcx.mir_for_trust_verification(owner).unwrap();
        let nominal = nominal_parameter::observe_nominal_parameter(tcx, owner, 0).unwrap();
        let source = nominal_body::observe_cached_nominal_body(nominal).unwrap();
        let capture = nominal_capture::capture_faithful_nominal_body(source);
        assert!(std::ptr::eq(capture.source().body(), snapshot));
        assert_eq!(capture.source().nominal().owner(), owner);
        assert_eq!(capture.function().body.arg_count, snapshot.arg_count);
        assert!(capture.function().contracts.is_empty());
        let before = capture.function() as *const trust_types::VerifiableFunction;
        // The existing MIR compatibility bridge consumes the actual immutable
        // produced function, never a decoded/re-lowered/synthesized replacement.
        let module = trust_ir_bridge::lower_to_trust_ir(capture.function()).unwrap();
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(before, capture.function() as *const trust_types::VerifiableFunction);
        println!(
            "actual faithful capture -> validated shared MIR-compat TrustIR: functions={} structs={} enums={}",
            module.functions.len(),
            module.structs.len(),
            module.enums.len()
        );

        use trust_ir::interpret::{
            InterpretOptions, InterpretValue, InterpretValueKind, Interpreter,
        };
        let argument_ty = module.func_type(module.functions[0].ty).unwrap().params[0].clone();
        let trust_ir::ty::Ty::Enum(id) = argument_ty.clone() else {
            panic!("actual enum argument required")
        };
        let definition = module.enums.iter().find(|e| e.id == id).unwrap();
        let discriminants = definition.effective_discriminants().unwrap();
        let tag_ty = definition.canonical_tag_repr().unwrap().ty();
        assert_eq!(discriminants.len(), 2);
        for (ordinal, discriminant) in discriminants.iter().copied().enumerate() {
            let argument = InterpretValue {
                ty: argument_ty.clone(),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(tag_ty.clone(), discriminant).unwrap(),
                ]),
            };
            let result = Interpreter::with_module(&module)
                .with_options(InterpretOptions {
                    fuel: 128,
                    max_call_depth: 4,
                    ..InterpretOptions::default()
                })
                .execute_func(module.functions[0].id, [argument])
                .unwrap();
            assert_eq!(result.host_calls, 0);
            assert_eq!(result.returns.len(), 1);
            assert_eq!(result.returns[0].as_bool(), Some(ordinal == 0));
        }
        println!(
            "actual shared-route IR execution: BOTH declared logical enum inputs PASS, zero host calls; no source/ABI/native proof claim"
        );
        rustc_driver::Compilation::Stop
    }
}
fn main() {
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("early custody refused: {error}");
        std::process::exit(75);
    }
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observer);
}
