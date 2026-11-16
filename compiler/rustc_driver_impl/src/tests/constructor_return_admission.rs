//! Trust: source-context admission, not a manually donated constructor identity.
// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.

struct Probe {
    completed: bool,
}

impl crate::Callbacks for Probe {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> crate::Compilation {
        use rustc_mir_transform::{
            TrustConstructorAdmissionRefusal as Refusal,
            TrustConstructorIdentityRefusal as Identity,
        };
        let rows = rustc_mir_transform::trust_constructor_return_admission_probe(tcx);
        let find = |type_suffix: Option<&str>, name: &str| {
            // Match actual typed owners; pretty-printed associated paths may
            // differ between inherent and trait impls and carry no authority.
            let mut owners = tcx.hir_body_owners().filter(|owner| {
                let id = owner.to_def_id();
                if !matches!(tcx.def_kind(id), rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn)
                    || tcx.item_name(id).as_str() != name { return false; }
                match (type_suffix, tcx.impl_of_assoc(id)) {
                    (None, None) => true,
                    (Some(suffix), Some(parent)) => {
                        let self_ty = tcx.type_of(parent).instantiate_identity().skip_normalization();
                        matches!(self_ty.kind(), rustc_middle::ty::Adt(adt, _) if tcx.def_path_str(adt.did()).ends_with(suffix))
                    }
                    _ => false,
                }
            });
            let id = owners
                .next()
                .unwrap_or_else(|| panic!("missing typed source {type_suffix:?}/{name}"));
            assert!(owners.next().is_none(), "ambiguous typed source owner");
            rows.iter()
                .find(|row| row.def_id == id.to_def_id())
                .unwrap_or_else(|| panic!("source inventory omitted {id:?}: {rows:#?}"))
        };
        for suffix in ["members::A", "members::B", "same_short::left::A", "same_short::right::A"] {
            let row = find(Some(suffix), "new");
            assert!(
                row.plain_total_drop_metadata,
                "must retain the REAL serde-skipped stamp: {row:?}"
            );
            assert_eq!(row.outcome, Ok(()), "original source must pass every actual mint guard");
        }
        for (owner, name, expected) in [
            (Some("Plain"), "generic", Identity::Generic),
            (Some("Plain"), "exported", Identity::Interposable),
            (Some("Plain"), "unsafe_signature", Identity::UnsafeSignature),
            (None, "free_function", Identity::NotAssociatedFunction),
            (Some("TraitOwner"), "make", Identity::NotLocalNongenericInherentImpl),
            (Some("UserDrop"), "new", Identity::OutputOwnerKindGenericsOrDrop),
            (Some("Padded"), "new", Identity::LayoutSizeOrAlignment),
        ] {
            assert_eq!(
                find(owner, name).outcome,
                Err(Refusal::Identity(expected)),
                "{owner:?}/{name}: all original identity/layout/no-Drop gates stay effective"
            );
        }
        assert!(!self.completed, "one actual compiler analysis");
        self.completed = true;
        crate::Compilation::Stop
    }
}

#[test]
fn constructor_mint_uses_actual_typed_preoptimization_source_and_transient_metadata() {
    // Trust: normal Bootstrap compiler-unit ownership supplies the matching std.
    // No external SDK, private metadata graft, self-skip or fake TyCtxt is used.
    let sysroot = std::env::var_os("TEST_SYSROOT")
        .map(std::path::PathBuf::from)
        .expect("run x.py test compiler/rustc_driver_impl (TEST_SYSROOT)");
    assert!(sysroot.is_dir());
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/tests/constructor_return_admission_subject.rs");
    assert!(source.is_file());
    let args = vec![
        "trustc-constructor-admission-unit".into(),
        source.to_str().unwrap().into(),
        "--sysroot".into(),
        sysroot.to_str().unwrap().into(),
        "--edition=2024".into(),
        "--crate-name=constructor_admission_subject".into(),
        "--crate-type=lib".into(),
        "--emit=metadata".into(),
        "-Ztrust-verify=off".into(),
        "-Ztrust-ir-lower=no".into(),
    ];
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(move || {
            let mut probe = Probe { completed: false };
            let status = crate::catch_with_exit_code(|| crate::run_compiler(&args, &mut probe));
            assert_eq!(status, std::process::ExitCode::SUCCESS);
            assert!(probe.completed, "all eleven source-context controls must execute");
        })
        .unwrap()
        .join()
        .unwrap();
}
