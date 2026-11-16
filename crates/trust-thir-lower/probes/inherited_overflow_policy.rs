#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_thir_lower;
use rustc_middle::ty::TyCtxt;
use trust_thir_lower::rmeta_entry::{inherited_overflow_refusal, EntryRefusal};
struct Probe;
impl rustc_driver::Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> rustc_driver::Compilation {
        let mut seen = std::collections::BTreeSet::new();
        for def in tcx.hir_body_owners() {
            let name = tcx.item_name(def.to_def_id()).to_string();
            let expected = match name.as_str() {
                "inherit_regular" | "inherit_generic" => true,
                "plain_regular" | "plain_generic" => false,
                _ => continue,
            };
            let actual = inherited_overflow_refusal(tcx, def);
            assert_eq!(actual, expected.then_some(EntryRefusal::InheritedOverflowChecks), "{name}");
            if let Some(refusal) = actual {
                assert_eq!(refusal.class(), "inherited-overflow-checks");
                assert!(refusal.reason().starts_with("inherited-overflow-checks("));
            }
            assert!(seen.insert(name));
        }
        assert_eq!(seen.len(), 4);
        println!("LOCAL-HIR mode={} checked=4 inherited=2 ordinary=2", tcx.sess.overflow_checks());
        rustc_driver::Compilation::Stop
    }
}
fn main() { let args: Vec<String> = std::env::args().collect(); rustc_driver::run_compiler(&args, &mut Probe); }
