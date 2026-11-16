//! Actual TyCtxt freeze-frame ownership and same-context epoch controls.
//! No layout, IR/body admission, source proof or compiler grade is requested.
#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_mir_extract;

use rustc_middle::ty;
use trust_mir_extract::ctfe_reentrancy as cr;

#[derive(Default)]
struct Observer {
    checked: usize,
}

impl rustc_driver::Callbacks for Observer {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let owner = tcx.hir_body_owners().find(|owner| {
            tcx.opt_item_name(owner.to_def_id()).is_some_and(|name| name.as_str() == "frame_owner")
        }).expect("one real fixture owner");
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_normalization().skip_binder();
        let [input] = signature.inputs() else { panic!("one actual fixture input") };
        let ty::Ref(_, input, _) = *input.kind() else { panic!("borrowed fixture input") };
        assert!(!cr::frozen());
        let outer = cr::enter_building(owner);
        assert!(cr::evaluation_admitted_here(tcx), "ordinary function cannot be a leaf CTFE body");
        let context = cr::LayoutQuerySafetyContext::new(tcx);
        assert!(context.is_safe(input), "named leaf array is initially evaluable");
        let inner = cr::enter();
        assert!(!cr::evaluation_admitted_here(tcx), "unnamed live owner forbids CTFE");
        assert!(!context.is_safe(input), "entry epoch revokes the completed leaf-array answer");
        drop(outer);
        assert!(cr::frozen(), "inner guard remains alive");
        assert!(!cr::evaluation_admitted_here(tcx), "dropping outer cannot remove the unnamed refusal");
        assert!(!context.is_safe(input), "same context must still decline while inner is live");
        drop(inner);
        assert!(!cr::frozen());
        assert!(context.is_safe(input), "reprove after both original guards have retired");
        self.checked += 1;
        println!("actual frame-owner cases=1; epoch/context decisions=4; live-inner-refusal=retained");
        // Ordinary fixture analysis must complete; an ill-typed fixture cannot
        // pass by stopping the compiler after this callback.
        rustc_driver::Compilation::Continue
    }
}

fn main() {
    unsafe { rustc_data_structures::jobserver::capture_early().expect("capture early") };
    let mut observer = Observer::default();
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut observer);
    assert_eq!(observer.checked, 1, "actual nonvacuous callback population");
}
