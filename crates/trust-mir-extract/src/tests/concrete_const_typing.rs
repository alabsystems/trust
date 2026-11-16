// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

struct Loader;
impl rustc_span::source_map::FileLoader for Loader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new("concrete_const_typing.rs")
    }
    fn read_file(&self, path: &Path) -> io::Result<String> {
        if !self.file_exists(path) {
            return Err(io::Error::other("unexpected fixture path"));
        }
        Ok("const fn deferred() -> usize { 2 }\nfn probe(_: [u8; deferred()]) {}".into())
    }
    fn read_binary_file(&self, _: &Path) -> io::Result<std::sync::Arc<[u8]>> {
        Err(io::Error::other("fixture does not read binary source"))
    }
    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct Probe {
    checked: bool,
}
impl rustc_driver::Callbacks for Probe {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.file_loader = Some(Box::new(Loader));
    }
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            if tcx.def_kind(owner) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            if tcx.item_name(owner.to_def_id()).as_str() != "probe" {
                continue;
            }
            let signature = tcx.fn_sig(owner).instantiate_identity().skip_norm_wip().skip_binder();
            let ty::Array(_, deferred) = signature.inputs()[0].kind() else {
                panic!("fixture must retain its array parameter");
            };
            crate::ctfe_reentrancy::assert_concrete_const_typing_controls(tcx, *deferred);
            assert!(!self.checked);
            self.checked = true;
        }
        rustc_driver::Compilation::Stop
    }
}

#[test]
fn concrete_const_typing_refuses_wrong_type_deferred_param_and_bound_inputs() {
    let mut probe = Probe::default();
    let args = vec![
        "rustc".into(),
        "concrete_const_typing.rs".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "-Ztrust-ir-lower=off".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    assert!(
        rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(&args, &mut probe);
        })
        .is_ok()
    );
    assert!(probe.checked, "the actual compiler callback must run");
}
