// Exact new producer module against an unchanged matching compiler namespace.
#![feature(rustc_private)]
extern crate rustc_attr_ir;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate trust_mir_extract;
extern crate trust_types;
#[path = "../../src/nominal_body.rs"]
mod nominal_body;
#[path = "../../src/nominal_parameter.rs"]
mod nominal_parameter;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use nominal_body::{NominalBodyRefusal as Refuse, observe_cached_nominal_body as body};
use nominal_parameter::observe_nominal_parameter as parameter;
use rustc_index::Idx;
use rustc_middle::mir::{Body, MirPhase, RuntimePhase};
use rustc_middle::ty::{InstanceKind, TyCtxt};
use rustc_span::def_id::LocalDefId;
pub use trust_mir_extract::{ctfe_reentrancy, extract_function_faithful};
type Provider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> Option<&'tcx Body<'tcx>>;
static ORIGINAL: OnceLock<Provider> = OnceLock::new();
static REENTRANT: AtomicUsize = AtomicUsize::new(0);
fn snapshot_provider<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> Option<&'tcx Body<'tcx>> {
    if let Ok(p) = parameter(tcx, owner, 0) {
        assert!(matches!(body(p), Err(Refuse::SnapshotNotCached)));
        REENTRANT.fetch_add(1, Ordering::Relaxed);
    }
    let original = ORIGINAL.get().unwrap();
    let name = tcx.item_name(owner.to_def_id());
    if name.as_str() == "unavailable" {
        return None;
    }
    if name.as_str() == "wrong_owner" {
        let other = tcx
            .hir_body_owners()
            .find(|d| tcx.opt_item_name(d.to_def_id()).is_some_and(|n| n.as_str() == "original"))
            .unwrap();
        return tcx.mir_for_trust_verification(other);
    }
    let result = original(tcx, owner)?;
    if !name.as_str().starts_with("wrong_") {
        return Some(result);
    }
    // Deliberately corrupt this real query's result in NEGATIVE controls only.
    // This does not model a trusted producer or establish arbitrary-provider
    // semantics; the public observation API accepts no supplied body.
    let mut changed = result.clone();
    match name.as_str() {
        "wrong_instance" => changed.source.instance = InstanceKind::Intrinsic(owner.to_def_id()),
        "wrong_promoted" => changed.source.promoted = Some(rustc_middle::mir::Promoted::new(0)),
        "wrong_population" => changed.arg_count += 1,
        "wrong_type" => {
            let local = changed.args_iter().next().unwrap();
            changed.local_decls[local].ty = tcx.types.bool;
        }
        "wrong_unused_type" => {
            let local = changed.args_iter().nth(1).unwrap();
            changed.local_decls[local].ty = tcx.types.u8;
        }
        "wrong_return" => changed.local_decls[rustc_middle::mir::RETURN_PLACE].ty = tcx.types.u8,
        "wrong_structure" => {
            changed.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK].terminator = None
        }
        "wrong_bound" => {
            let decl = changed.local_decls[rustc_middle::mir::RETURN_PLACE].clone();
            while changed.local_decls.len() <= 4096 {
                changed.local_decls.push(decl.clone());
            }
        }
        _ => panic!("unknown negative control"),
    }
    Some(tcx.arena.alloc(changed))
}
struct Observer;
impl rustc_driver::Callbacks for Observer {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_, providers| {
            assert!(ORIGINAL.set(providers.queries.mir_for_trust_verification).is_ok());
            providers.queries.mir_for_trust_verification = snapshot_provider;
        });
    }
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let find = |name: &str| {
            tcx.hir_body_owners()
                .find(|d| tcx.opt_item_name(d.to_def_id()).is_some_and(|n| n.as_str() == name))
                .unwrap()
        };
        // Match the compiler's real analysis-seam protocol: complete the
        // compact pre-steal graph oracle BEFORE optimizing any fixture body.
        let _ = tcx.trust_mir_mutually_recursive_functions(());
        let owner = find("original");
        assert!(matches!(body(parameter(tcx, owner, 0).unwrap()), Err(Refuse::SnapshotNotCached)));
        let snapshot = tcx.mir_for_trust_verification(owner).unwrap();
        let captured = body(parameter(tcx, owner, 0).unwrap()).unwrap();
        assert!(std::ptr::eq(captured.body(), snapshot));
        assert_eq!(captured.observed_phase(), MirPhase::Runtime(RuntimePhase::PostCleanup));
        assert_eq!(captured.observed_pass_count(), snapshot.pass_count);
        assert_eq!(captured.argument_local(), snapshot.args_iter().next().unwrap());
        assert_eq!(
            snapshot.local_decls[captured.argument_local()].ty,
            captured.nominal().source_ty()
        );
        assert_eq!(captured.authored_clause_count(), 0);
        assert!(std::ptr::eq(
            captured.source_attributes(),
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner))
        ));
        assert_eq!(captured.nominal().owner_key(), tcx.def_path_hash(snapshot.source.def_id()));
        assert_eq!(
            captured.nominal().nominal_key(),
            tcx.def_path_hash(captured.nominal().declaration().did())
        );
        let converted = captured.extract_faithful();
        assert_eq!(converted.body.arg_count, snapshot.arg_count);
        assert!(converted.contracts.is_empty());
        let freeze = ctfe_reentrancy::enter_building(owner);
        assert!(matches!(body(parameter(tcx, owner, 0).unwrap()), Err(Refuse::MirBuilding)));
        drop(freeze);
        let phase = captured.observed_phase();
        let passes = captured.observed_pass_count();
        let _ = tcx.optimized_mir(owner.to_def_id());
        assert_eq!(captured.observed_phase(), phase);
        assert_eq!(captured.observed_pass_count(), passes);
        assert!(body(parameter(tcx, owner, 0).unwrap()).is_ok());
        let fresh = find("stolen");
        let _ = tcx.optimized_mir(fresh.to_def_id());
        assert!(matches!(body(parameter(tcx, fresh, 0).unwrap()), Err(Refuse::SnapshotNotCached)));
        let optimized = tcx.mir_for_trust_verification(fresh).unwrap();
        assert_eq!(optimized.phase, MirPhase::Runtime(RuntimePhase::Optimized));
        assert!(matches!(
            body(parameter(tcx, fresh, 0).unwrap()),
            Err(Refuse::SnapshotPhase(MirPhase::Runtime(RuntimePhase::Optimized)))
        ));
        for name in ["authored", "legacy_authored", "loop_authored"] {
            let owner = find(name);
            tcx.mir_for_trust_verification(owner).unwrap();
            assert!(
                matches!(body(parameter(tcx, owner, 0).unwrap()), Err(Refuse::AuthoredContracts)),
                "{name}"
            );
        }
        let other = find("other");
        tcx.mir_for_trust_verification(other).unwrap();
        let other = body(parameter(tcx, other, 0).unwrap()).unwrap();
        assert_eq!(other.body().arg_count, 2);
        assert!(!other.nominal().same_parameter_as(captured.nominal()));
        for (name, expected) in [
            ("wrong_owner", Refuse::SourceIdentity),
            ("wrong_instance", Refuse::SourceIdentity),
            ("wrong_promoted", Refuse::SourceIdentity),
            ("wrong_population", Refuse::ArgumentPopulation),
            ("wrong_type", Refuse::ArgumentType),
            ("wrong_unused_type", Refuse::ArgumentType),
            ("wrong_return", Refuse::ReturnType),
            ("wrong_structure", Refuse::BodyStructure),
            ("wrong_bound", Refuse::BodyBound),
        ] {
            let owner = find(name);
            let _ = tcx.mir_for_trust_verification(owner).unwrap();
            assert!(
                matches!(body(parameter(tcx,owner,0).unwrap()),Err(actual) if actual==expected),
                "{name}"
            );
        }
        let unavailable = find("unavailable");
        assert!(tcx.mir_for_trust_verification(unavailable).is_none());
        assert!(matches!(
            body(parameter(tcx, unavailable, 0).unwrap()),
            Err(Refuse::SnapshotUnavailable)
        ));
        assert!(REENTRANT.load(Ordering::Relaxed) >= 1);
        println!(
            "actual query snapshot phase={:?} pass_count={} locals={} blocks={} clauses=0",
            captured.observed_phase(),
            captured.observed_pass_count(),
            captured.body().local_decls.len(),
            captured.body().basic_blocks.len()
        );
        println!(
            "live immutable elaborated body: 36 assertions plus real reentrant provider refusals PASS; historical phase/body/grade authority OPEN"
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
