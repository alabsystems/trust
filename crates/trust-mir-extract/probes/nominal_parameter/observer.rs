// Component qualification of the exact new module against a coherent private
// compiler namespace. Ordinary unverified Rust, not compiler/source evidence.
#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
use std::collections::BTreeMap;

use nominal_parameter::{NominalParameterRefusal as Refuse, observe_nominal_parameter as observe};
use rustc_middle::ty::TyCtxt;
struct Observer;
impl rustc_driver::Callbacks for Observer {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let defs: BTreeMap<_, _> = tcx
            .hir_body_owners()
            .filter(|d| tcx.def_kind(*d) == rustc_hir::def::DefKind::Fn)
            .map(|d| (tcx.item_name(d.to_def_id()).to_string(), d))
            .collect();
        if let (Some(left), Some(right)) = (defs.get("same_path_left"), defs.get("same_path_right"))
        {
            let left = observe(tcx, *left, 0).unwrap();
            let right = observe(tcx, *right, 0).unwrap();
            assert_eq!(
                format!(
                    "{}::{}",
                    tcx.crate_name(left.declaration().did().krate),
                    tcx.def_path(left.declaration().did()).to_string_no_crate_verbose()
                ),
                format!(
                    "{}::{}",
                    tcx.crate_name(right.declaration().did().krate),
                    tcx.def_path(right.declaration().did()).to_string_no_crate_verbose()
                )
            );
            assert_ne!(left.nominal_key(), right.nominal_key());
            assert!(!left.same_nominal_as(&right));
            assert!(!left.same_parameter_as(&right));
            println!("same canonical crate/item names: 4 live identity assertions PASS");
            return rustc_driver::Compilation::Stop;
        }
        let original = observe(tcx, defs["original"], 0).unwrap();
        let again = observe(tcx, defs["original"], 0).unwrap();
        let other = observe(tcx, defs["other_owner"], 0).unwrap();
        let first = observe(tcx, defs["two_positions"], 0).unwrap();
        let second = observe(tcx, defs["two_positions"], 1).unwrap();
        let alias = observe(tcx, defs["alias"], 0).unwrap();
        let lookalike = observe(tcx, defs["lookalike"], 0).unwrap();
        assert!(original.same_parameter_as(&again));
        assert!(original.same_nominal_as(&other));
        assert!(!original.same_parameter_as(&other));
        assert!(first.same_nominal_as(&second));
        assert!(!first.same_parameter_as(&second));
        assert!(original.same_nominal_as(&alias));
        assert!(!original.same_nominal_as(&lookalike));
        assert_eq!(original.argument(), 0);
        assert_eq!(original.owner(), defs["original"]);
        assert_eq!(original.owner_key(), tcx.def_path_hash(defs["original"].to_def_id()));
        assert_eq!(original.nominal_key(), tcx.def_path_hash(original.declaration().did()));
        assert_eq!(
            original.source_ty(),
            tcx.fn_sig(defs["original"]).instantiate_identity().skip_binder().inputs()[0]
        );
        assert_ne!(original.nominal_key(), lookalike.nominal_key());
        for (name, expected) in [
            ("reference", Refuse::GenericFunction),
            ("static_reference", Refuse::NotByValueEnum),
            ("late", Refuse::GenericFunction),
            ("scalar", Refuse::NotByValueEnum),
            ("structure", Refuse::NotByValueEnum),
            ("payload", Refuse::PayloadVariant),
            ("generic", Refuse::GenericFunction),
            ("generic_enum", Refuse::GenericEnum),
            ("empty", Refuse::VariantBound),
        ] {
            assert!(matches!(observe(tcx,defs[name],0),Err(actual) if actual==expected), "{name}");
        }
        assert!(matches!(observe(tcx, defs["original"], 1), Err(Refuse::ArgumentBound)));
        assert!(matches!(observe(tcx, defs["arity_bound"], 0), Err(Refuse::ArgumentBound)));
        assert!(matches!(observe(tcx, defs["variant_bound"], 0), Err(Refuse::VariantBound)));
        assert!(matches!(
            observe(tcx, tcx.parent(defs["original"].to_def_id()).as_local().unwrap(), 0),
            Err(Refuse::NotFunction)
        ));
        let signed = observe(tcx, defs["signed"], 0).unwrap();
        assert_ne!(signed.nominal_key(), original.nominal_key());
        assert!(!signed.same_nominal_as(&original));
        println!(
            "nominal parameter live query: 28 original identity/refusal assertions PASS; no body/capture/grade authority"
        );
        rustc_driver::Compilation::Stop
    }
}
fn main() {
    // FIRST operation: preserve inherited GNU jobserver custody.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("early custody refused: {error}");
        std::process::exit(75);
    }
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Observer);
}
