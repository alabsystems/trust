// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compiler-owned mode separation over the existing no_core Expr fixture.
//!
//! These are real rustc MIR bodies, not authored VerifiableFunction/type records.
//! The fixture is a miniature using raw pointers: this tests extraction-mode
//! separation, not the production literal helper, Arc layout, or Rust refinement.

use super::*;

#[derive(Default)]
struct ModeCallbacks {
    functions: BTreeMap<String, (VerifiableFunction, VerifiableFunction)>,
}

impl rustc_driver::Callbacks for ModeCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(InMemoryExprFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for def_id in tcx.hir_body_owners() {
            let did = def_id.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let Some(name) = tcx.opt_item_name(did) else { continue };
            let name = name.to_string();
            if !matches!(name.as_str(), "make_exprkind" | "wrap_expr" | "build_sort") {
                continue;
            }
            let body = tcx.optimized_mir(did);
            // Each public entry opens its own DatatypeDefScope. The faithful
            // entry also owns the RAII mode guard on this compiler callback thread.
            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            let logical_after = extract_function(tcx, body);
            assert_eq!(logical.body.return_ty, logical_after.body.return_ty);
            assert_eq!(logical.body.datatype_defs, logical_after.body.datatype_defs);
            assert_eq!(
                logical.body.locals.iter().map(|local| &local.ty).collect::<Vec<_>>(),
                logical_after.body.locals.iter().map(|local| &local.ty).collect::<Vec<_>>(),
                "faithful extraction must not leak its mode into the next body"
            );
            assert!(self.functions.insert(name, (logical, faithful)).is_none());
        }
        Compilation::Stop
    }
}

fn extract_modes() -> BTreeMap<String, (VerifiableFunction, VerifiableFunction)> {
    let mut callbacks = ModeCallbacks::default();
    // The existing fixture is self-contained: no staged standard library and no
    // semantic/evidence flags. Embedded compilation supplies no proof authority.
    let args = vec![
        "rustc".to_string(),
        EXPR_FIXTURE_PATH.to_string(),
        "--crate-name".to_string(),
        "clean_kernel".to_string(),
        "--crate-type=lib".to_string(),
        "--edition=2021".to_string(),
        "-Zmir-opt-level=3".to_string(),
        "-Zno-codegen".to_string(),
        "-Zcodegen-backend=dummy".to_string(),
        "-Ainternal_features".to_string(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the existing Expr fixture");
    assert_eq!(
        callbacks.functions.keys().map(String::as_str).collect::<Vec<_>>(),
        ["build_sort", "make_exprkind", "wrap_expr"]
    );
    callbacks.functions
}

fn resolve<'a>(function: &'a VerifiableFunction, ty: &'a Ty) -> &'a Ty {
    if matches!(ty, Ty::Datatype { variants, .. } if variants.is_empty()) {
        trust_types::datatype_marker_definition(&function.body.datatype_defs, ty)
            .expect("compiler-owned marker must retain its own complete definition")
    } else {
        ty
    }
}

fn physical_parts<'a>(
    function: &'a VerifiableFunction,
    ty: &'a Ty,
    suffix: &str,
    kind: trust_types::AdtKind,
) -> (&'a [(String, Ty)], &'a [trust_types::VariantDef]) {
    let Ty::Adt { name, fields, variants, adt_kind, .. } = resolve(function, ty) else {
        panic!("faithful {suffix} must resolve to a physical Adt, got {:?}", resolve(function, ty));
    };
    assert!(name.ends_with(suffix), "unexpected physical type {name}");
    assert_eq!(adt_kind.as_ref(), Some(&kind));
    (fields, variants)
}

fn variant_fields<'a>(variants: &'a [trust_types::VariantDef], name: &str) -> &'a [(String, Ty)] {
    &variants.iter().find(|variant| variant.name == name).expect("fixture variant").fields
}

fn assert_raw_child(function: &VerifiableFunction, ty: &Ty, suffix: &str) {
    let Ty::RawPtr { mutable: false, pointee } = ty else {
        panic!("recursive field must retain the actual raw pointer, got {ty:?}");
    };
    let Ty::Adt { name, .. } = resolve(function, pointee) else {
        panic!("recursive pointee must have its own physical definition");
    };
    assert!(name.ends_with(suffix), "wrong recursive pointee {name}");
}

#[test]
fn faithful_kernel_datatypes_keep_physical_fields_and_restore_logical_mode() {
    let functions = extract_modes();

    let (logical, faithful) = &functions["build_sort"];
    let logical_level = &logical.body.locals[1].ty;
    let (_, logical_variants) = resolve_datatype(logical_level, &logical.body.datatype_defs);
    let logical_succ = &logical_variants.iter().find(|(name, _)| name == "Succ").unwrap().1;
    assert!(matches!(&logical_succ[0].1, Ty::Datatype { variants, .. } if variants.is_empty()));
    let (_, variants) = physical_parts(
        faithful,
        &faithful.body.locals[1].ty,
        "level::Level",
        trust_types::AdtKind::Enum,
    );
    assert_eq!(
        variants
            .iter()
            .map(|variant| (variant.name.as_str(), variant.discriminant))
            .collect::<Vec<_>>(),
        [("Zero", 0), ("Succ", 1), ("Max", 2), ("IMax", 3), ("Param", 4)]
    );
    assert_raw_child(faithful, &variant_fields(variants, "Succ")[0].1, "level::Level");
    for name in ["Max", "IMax"] {
        let fields = variant_fields(variants, name);
        assert_eq!(fields.len(), 2);
        for (_, ty) in fields {
            assert_raw_child(faithful, ty, "level::Level");
        }
    }

    let (logical, faithful) = &functions["make_exprkind"];
    let (_, logical_variants) =
        resolve_datatype(&logical.body.return_ty, &logical.body.datatype_defs);
    let logical_app = &logical_variants.iter().find(|(name, _)| name == "App").unwrap().1;
    assert!(
        logical_app
            .iter()
            .all(|(_, ty)| matches!(ty, Ty::Datatype { variants, .. } if variants.is_empty()))
    );
    let (_, variants) = physical_parts(
        faithful,
        &faithful.body.return_ty,
        "expr::kind::ExprKind",
        trust_types::AdtKind::Enum,
    );
    assert_eq!(
        variants.iter().map(|variant| variant.name.as_str()).collect::<Vec<_>>(),
        ["BVar", "Sort", "Const", "App", "Lam", "Let", "Lit", "Proj", "SProp", "CubicalPath"]
    );
    assert_eq!(variant_fields(variants, "BVar")[0].1, Ty::Int { width: 32, signed: false });
    let app = variant_fields(variants, "App");
    assert_eq!(app.len(), 2);
    for (_, ty) in app {
        assert_raw_child(faithful, ty, "expr::Expr");
    }

    let (logical, faithful) = &functions["wrap_expr"];
    let (_, logical_variants) =
        resolve_datatype(&logical.body.return_ty, &logical.body.datatype_defs);
    assert_eq!(logical_variants.len(), 1);
    assert!(
        matches!(&logical_variants[0].1[1].1, Ty::Datatype { variants, .. } if variants.is_empty())
    );
    let (fields, variants) = physical_parts(
        faithful,
        &faithful.body.return_ty,
        "expr::Expr",
        trust_types::AdtKind::Struct,
    );
    assert!(variants.is_empty(), "the physical struct must not invent an enum constructor");
    assert_eq!(fields.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(), ["kind", "meta"]);
    physical_parts(faithful, &fields[0].1, "expr::kind::ExprKind", trust_types::AdtKind::Enum);
    let (meta_fields, _) = physical_parts(
        faithful,
        &fields[1].1,
        "expr::meta::ExprMeta",
        trust_types::AdtKind::Struct,
    );
    assert_eq!(meta_fields, &[("0".to_string(), Ty::Int { width: 64, signed: false })]);
}
