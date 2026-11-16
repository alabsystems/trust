// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0
//! Actual rustc-private producer/consumer controls. Run through the explicitly
//! source-bound SDK component operator; this does not replace bootstrap checking.
#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;

use rustc_driver::Compilation;
use rustc_interface::interface::{Compiler, Config};
use trust_types::{VcKind, VerifiableFunction};
use trust_vcgen::{PrimitiveDecimalStringTable, VcgenContext};

#[path = "fixtures/primitive_decimal_source.rs"]
mod native_source;

#[derive(Default)]
struct Capture {
    rows: BTreeMap<String, (VerifiableFunction, PrimitiveDecimalStringTable)>,
    bits: u32,
}

impl rustc_driver::Callbacks for Capture {
    fn config(&mut self, _config: &mut Config) {}

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        self.bits = tcx.data_layout.pointer_size().bits() as u32;
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let plain = trust_mir_extract::extract_function_with_contract_bundle(tcx, body, None);
            let (with, _, table) =
                trust_mir_extract::extract_function_with_compiler_facts(tcx, body, None);
            assert_eq!(serde_json::to_vec(&plain).unwrap(), serde_json::to_vec(&with).unwrap());
            assert_eq!(
                trust_types::stable_model_json_bytes(&plain).unwrap(),
                trust_types::stable_model_json_bytes(&with).unwrap()
            );
            self.rows.insert(tcx.item_name(did).to_string(), (with, table));
        }
        Compilation::Stop
    }
}

fn capture() -> Capture {
    let sysroot =
        PathBuf::from(std::env::var_os("TRUST_TEST_SYSROOT").expect("explicit matching SDK"));
    assert!(sysroot.join("bin/trustc").is_file());
    let compiler = std::process::Command::new(sysroot.join("bin/trustc"))
        .arg("-vV")
        .output()
        .expect("selected compiler identity");
    assert!(compiler.status.success());
    let identity = String::from_utf8(compiler.stdout).unwrap();
    assert!(identity.contains(rustc_interface::util::rustc_version_str().unwrap().trim()));
    let source = PathBuf::from(env!("PRIMITIVE_DECIMAL_FIXTURE"));
    let mut callbacks = Capture::default();
    let args = vec![
        "trustc".into(),
        source.to_string_lossy().into_owned(),
        "--crate-name=primitive_decimal_source".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
        "-Zinline-mir=no".into(),
        "-Cdebug-assertions=yes".into(),
        "-Zno-codegen".into(),
        "-Ztrust-verify=off".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        sysroot.to_string_lossy().into_owned(),
    ];
    let outcome =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callbacks));
    assert!(outcome.is_ok(), "real fixture must compile and reach after_analysis");
    callbacks
}

#[test]
fn primitive_decimal_real_source_producer_and_formula_boundaries() {
    let capture = capture();
    assert_eq!(capture.bits, 64, "this native qualification binds the actual 64-bit target");
    for name in [
        "requested_capacity",
        "bounded_allocation",
        "format_number",
        "direct_heap_mutation",
        "alias_heap_mutation",
        "moved_heap_mutation",
        "replaced_string",
        "numeric_return_reassigned",
        "real_overflow",
    ] {
        assert!(!capture.rows[name].1.is_empty(), "{name}: actual primitive call authority");
    }
    for name in [
        "custom_display",
        "custom_trait",
        "generic_display",
        "float_display",
        "extra_reference",
        "foreign_call",
    ] {
        assert!(capture.rows[name].1.is_empty(), "{name}: unsupported source gets no authority");
    }
    let mut observations = Vec::new();
    let mut failures = Vec::new();
    for (name, (func, table)) in &capture.rows {
        let plain_context = VcgenContext::for_function(func.def_path.clone())
            .with_target_pointer_bits(Some(capture.bits));
        let context = plain_context.clone().with_primitive_decimal_strings(table.clone(), func);
        let plain = trust_vcgen::generate_vcs_with_context(func, &plain_context);
        let bounded = trust_vcgen::generate_vcs_with_context(func, &context);
        let plain_bytes = serde_json::to_vec(&plain).unwrap();
        let bounded_bytes = serde_json::to_vec(&bounded).unwrap();
        if matches!(
            name.as_str(),
            "direct_heap_mutation"
                | "alias_heap_mutation"
                | "moved_heap_mutation"
                | "replaced_string"
        ) {
            if plain_bytes != bounded_bytes {
                failures.push(format!("{name}: mutation withdraws all new length facts"));
            }
        }
        let selected = bounded
            .iter()
            .filter(|vc| {
                if name == "bounded_allocation" || name == "format_number" {
                    matches!(&vc.kind, VcKind::UnboundedAllocation { callee, .. } if callee.contains("with_capacity"))
                } else {
                    matches!(vc.kind, VcKind::ArithmeticOverflow { .. })
                }
            })
            .collect::<Vec<_>>();
        let certified =
            selected.iter().filter(|vc| trust_certify::certify_vc(vc).is_some()).count();
        if let Some(directory) = std::env::var_os("PRIMITIVE_DECIMAL_EVIDENCE") {
            let path = PathBuf::from(directory).join(format!("source-vcs-{name}.json"));
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)
                .expect("fresh owned source evidence file");
            // Stream typed values: Value is not a lossless wide-integer bridge.
            file.write_all(b"{\"function\":").unwrap();
            serde_json::to_writer_pretty(&mut file, func).unwrap();
            file.write_all(b",\"plain_vcs\":").unwrap();
            serde_json::to_writer_pretty(&mut file, &plain).unwrap();
            file.write_all(b",\"bounded_vcs\":").unwrap();
            serde_json::to_writer_pretty(&mut file, &bounded).unwrap();
            file.write_all(b",\"selected_refusals\":").unwrap();
            serde_json::to_writer(
                &mut file,
                &selected.iter().map(|vc| vc.kernel_authority_refusal()).collect::<Vec<_>>(),
            )
            .unwrap();
            file.write_all(b",\"scope\":\"Actual source/VC observations only; no table authority, proof or P5 claim\"}\n").unwrap();
        }
        observations.push(serde_json::json!({"function":name,"has_authority":!table.is_empty(),
            "vc_count":bounded.len(),"selected":selected.len(),"certified":certified,
            "same_vcs_without_table":plain_bytes==bounded_bytes}));
        println!("PRIMITIVE_DECIMAL_SOURCE {}", observations.last().unwrap());
        if matches!(name.as_str(), "requested_capacity" | "bounded_allocation" | "format_number") {
            if selected.is_empty() {
                failures.push(format!("{name}: actual nonvacuous selected formula"));
            }
            if certified != selected.len() {
                failures.push(format!(
                    "{name}: selected formulas kernel-check ({certified}/{})",
                    selected.len()
                ));
            }
            if plain_bytes == bounded_bytes {
                failures.push(format!("{name}: actual source consumes new table"));
            }
        } else if matches!(
            name.as_str(),
            "real_overflow"
                | "numeric_return_reassigned"
                | "direct_heap_mutation"
                | "alias_heap_mutation"
                | "moved_heap_mutation"
                | "replaced_string"
                | "custom_display"
                | "custom_trait"
                | "foreign_call"
        ) {
            // A compiler may retain a separate SSA temporary for the first
            // length before the user's variable is reassigned. A true bound on
            // that old temporary is fine; it must not certify the later overflow.
            if selected.is_empty() || certified == selected.len() {
                failures.push(format!(
                    "{name}: actual invalid arithmetic stays nonvacuous and not all certified"
                ));
            }
        }
    }
    println!(
        "PRIMITIVE_DECIMAL_COMPONENT_SCOPE {}",
        serde_json::json!({
        "target_bits":capture.bits,"functions":observations,
        "scope":"Actual typed extraction and these formulas only; no whole compiler/bootstrap, translation, SDK or P5 proof claim"})
    );
    assert!(failures.is_empty(), "actual source controls failed: {failures:?}");
}

#[test]
fn primitive_decimal_actual_native_inputs_and_mutation_failures() {
    assert_eq!(native_source::real_ty_format_number(0), "0");
    assert_eq!(native_source::real_ty_format_number(1), "1");
    assert_eq!(native_source::real_ty_format_number(usize::MAX), "18,446,744,073,709,551,615");
    for value in [0, 1, usize::MAX] {
        assert!(native_source::requested_capacity(value) <= 26);
        assert!(
            native_source::bounded_allocation(value).capacity()
                >= native_source::requested_capacity(value)
        );
    }
    for (name, run) in [
        ("direct", native_source::direct_heap_mutation as fn(usize) -> usize),
        ("alias", native_source::alias_heap_mutation),
        ("move", native_source::moved_heap_mutation),
        ("replace", native_source::replaced_string),
        ("numeric", native_source::numeric_return_reassigned),
        ("overflow", native_source::real_overflow),
    ] {
        assert!(
            std::panic::catch_unwind(|| run(0)).is_err(),
            "{name}: real invalid input must panic"
        );
    }
    assert!(std::panic::catch_unwind(native_source::custom_display).is_err());
    assert!(std::panic::catch_unwind(|| native_source::custom_trait(0)).is_err());
    assert!(std::panic::catch_unwind(|| native_source::foreign_call(0)).is_err());
}
