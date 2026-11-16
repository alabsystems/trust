//! Trust: source Freeze goals checked by the current-source compiler unit.
//!
//! Run-make retains the public ABI/validator controls; it must not require a
//! separately installed rustc-private metadata cohort before stage2 exists.

// Trust: compile the unchanged production predicate, without a public test API
// or a copied trait rule. The ambient enter_building guard stays below.
#[path = "../../../../crates/trust-thir-lower/src/shared_receiver_freeze.rs"]
mod shared_receiver_freeze;

struct Probe {
    completed: bool,
}

impl crate::Callbacks for Probe {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> crate::Compilation {
        use rustc_middle::ty;
        let mut checked = std::collections::BTreeSet::new();
        for owner in tcx.hir_body_owners() {
            let name = tcx.item_name(owner.to_def_id()).to_string();
            let expected = match name.as_str() {
                "freeze_gat" | "plain_scalar" => true,
                "mutable_gat" | "unknown_gat" | "mutable_direct" | "shared_cell"
                | "const_generic" | "opaque_root" | "opaque_field" => false,
                _ => continue,
            };
            let sig = tcx.fn_sig(owner).instantiate_identity().skip_binder();
            let [arg] = sig.inputs() else { panic!("one source argument") };
            let ty::Ref(_, pointee, _) = arg.kind() else { panic!("source reference") };
            // Exercise the same analysis-time query discipline as the producer.
            let _freeze = trust_mir_extract::ctfe_reentrancy::enter_building(owner);
            let actual = shared_receiver_freeze::source_receiver_snapshot_is_freeze(tcx, *pointee);
            assert_eq!(actual, expected, "source Freeze evidence for {name}: {pointee:?}");
            assert!(checked.insert(name));
        }
        assert_eq!(checked.len(), 9, "all source controls must execute");
        assert!(!self.completed, "source analysis must execute exactly once");
        self.completed = true;
        crate::Compilation::Stop
    }
}

#[test]
fn source_freeze_goals_use_the_current_compiler_and_matching_sysroot() {
    // Trust: Bootstrap's Mode::Rustc unit owner supplies the std matching the
    // in-process driver. Missing setup refuses; no SDK fallback or self-skip.
    let sysroot = std::env::var_os("TEST_SYSROOT")
        .map(std::path::PathBuf::from)
        .expect("run through x.py test compiler/rustc_driver_impl (TEST_SYSROOT)");
    assert!(sysroot.is_dir(), "canonical TEST_SYSROOT is not a directory");
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/tests/shared_receiver_freeze_subject.rs");
    assert!(source.is_file(), "tracked source Freeze subject is missing");
    let args = vec![
        "trustc-source-freeze-unit".into(),
        source.to_str().expect("source path must be Unicode").into(),
        "--sysroot".into(),
        sysroot.to_str().expect("TEST_SYSROOT must be Unicode").into(),
        "--edition=2024".into(),
        "--crate-type=lib".into(),
        "--emit=metadata".into(),
        "-Ztrust-verify=off".into(),
        "-Ztrust-ir-lower=no".into(),
    ];
    let mut probe = Probe { completed: false };
    let status = crate::catch_with_exit_code(|| crate::run_compiler(&args, &mut probe));
    assert_eq!(status, std::process::ExitCode::SUCCESS, "source fixture compilation failed");
    assert!(probe.completed, "all nine source controls must actually execute");
}
