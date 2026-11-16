// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Exercise the enum-field reader on actual bound types from callback signatures.

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::*;

const PATH: &str = "bound_enum_fields.rs";
const SOURCE: &str = r#"
#![allow(dead_code)]
enum Thin<'a> { Empty, Value(&'a &'a u32) }
enum Slice<'a> { Empty, Value(&'a [&'a ()]) }
enum StaticSlice { Empty, Value(&'static [&'static ()]) }
fn bound_thin(_: &dyn for<'a> Fn(&'a Thin<'a>)) {}
fn bound_slice(_: &dyn for<'a> Fn(&'a Slice<'a>)) {}
fn static_slice(_: &dyn Fn(&StaticSlice)) {}
"#;

struct Loader;

impl rustc_span::source_map::FileLoader for Loader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(SOURCE.to_string())
        } else {
            Err(io::Error::other("unexpected enum-field fixture path"))
        }
    }

    fn read_binary_file(&self, _: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("fixture does not read binary source"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct Probe {
    observed: BTreeMap<String, bool>,
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
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            if !matches!(name.as_str(), "bound_thin" | "bound_slice" | "static_slice") {
                continue;
            }
            let signature = tcx.fn_sig(did).instantiate_identity().skip_norm_wip().skip_binder();
            let TyKind::Ref(_, callback, _) = signature.inputs()[0].kind() else {
                panic!("fixture callback must be a reference");
            };
            let TyKind::Dynamic(predicates, _) = callback.kind() else {
                panic!("fixture callback must be a trait object");
            };
            // Keep the callback's binder intact in the selected argument type.
            // These are precisely the input types that reached the real crash.
            let principal = predicates.principal().expect("Fn principal").skip_binder();
            let argument = principal
                .args
                .iter()
                .find_map(|arg| match arg.as_type()?.kind() {
                    TyKind::Tuple(fields) if fields.len() == 1 => Some(fields[0]),
                    _ => None,
                })
                .expect("single callback argument");
            let TyKind::Ref(_, enum_ty, _) = argument.kind() else {
                panic!("callback argument must refer to an enum");
            };
            let TyKind::Adt(definition, args) = enum_ty.kind() else {
                panic!("callback pointee must be an enum");
            };
            let field = definition
                .variants()
                .iter()
                .find(|variant| variant.name.as_str() == "Value")
                .expect("Value variant")
                .fields
                .iter()
                .next()
                .expect("Value payload field")
                .ty(tcx, *args)
                .skip_normalization();
            let TyKind::Ref(_, pointee, _) = field.kind() else {
                panic!("payload must be a reference");
            };
            assert_eq!(pointee.has_escaping_bound_vars(), name != "static_slice");
            let expected = name == "bound_thin";
            let env = ty::TypingEnv::fully_monomorphized();
            if expected {
                // Independent rustc answer: the bound reference is still Sized.
                assert!(pointee.is_sized(tcx, env));
            } else {
                assert!(matches!(pointee.kind(), TyKind::Slice(_)));
            }
            let mut context = TyLoweringCtx::with_typing_env(env);
            let modeled = convert_ty_inner(tcx, field, &mut context);
            let actual = extractor_enum_variant_field_admissible(tcx, field, &modeled, &context);
            assert_eq!(actual, expected, "{name}");
            assert!(self.observed.insert(name, actual).is_none());
        }
        rustc_driver::Compilation::Stop
    }
}

#[test]
fn real_bound_enum_fields_keep_sized_references_and_decline_slices() {
    let mut probe = Probe::default();
    let args = vec![
        "rustc".into(),
        PATH.into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "-Ztrust-ir-lower=off".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        crate::tests::compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&args, &mut probe);
    });
    assert!(result.is_ok(), "real callback fixture must compile");
    assert_eq!(
        probe.observed,
        BTreeMap::from([
            ("bound_slice".into(), false),
            ("bound_thin".into(), true),
            ("static_slice".into(), false),
        ])
    );
}
