// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Rustc's tuple layouts on the faithful extraction lane, end to end (2026-09-29).
//!
//! `trust_types::Ty::Tuple` carries no layout, so a tuple field's address had no byte
//! offset on any lane: the bridge guessed `index * size_of(field)` until 2026-09-28 and
//! has named an unknown offset since. The faithful lane now records rustc's own
//! `layout_of` answer per concrete tuple (`VerifiableFunction::tuple_layouts`), and the
//! bridge declares it in the module. These rows compile real Rust and check:
//!
//! * the faithful body carries EXACTLY rustc's layout, asked of rustc independently
//!   here — including a tuple rustc reorders — and the logical (verifier) body
//!   carries none, so no shipped verifier pin moves;
//! * a tuple over a type parameter carries no row (there is no layout to ask for);
//! * the bridge lowers the field address at rustc's offset, and the reference
//!   interpreter reads the right field back through it.

#![feature(rustc_private)]
// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): these tests run the compiler in process;
// their binary captures its scheduler at native entry (tests/support/native_test_entry.rs).
#![cfg_attr(
    any(target_os = "linux", target_os = "macos"),
    feature(test, custom_test_frameworks, exitcode_exit_method)
)]
#![cfg_attr(any(target_os = "linux", target_os = "macos"), test_runner(native_test_entry::main))]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustc_driver::Compilation;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty as IrTy;
use trust_types::{Ty, VerifiableFunction};

const FIXTURE_PATH: &str = "faithful_tuple_layouts_fixture.rs";

const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn pair_second(t: (u32, u8)) -> u8 {
    let p = &t.1;
    *p
}

pub fn triple_middle(t: (u8, u32, u16)) -> u32 {
    let p = &t.1;
    *p
}

pub fn generic_second<T: Copy>(t: (T, u8)) -> u8 {
    let p = &t.1;
    *p
}
"#;

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected tuple-layout fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in this fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

// The same explicit sysroot overrides as `producer_lowering_gaps.rs` (an integration
// target cannot call the library's private cfg(test) helper), and the same refusal of
// a proven driver version mismatch.
fn compiler_sysroot() -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
    // Bootstrap exports RUSTC_SYSROOT (and a tool build SYSROOT) for the compiler
    // BUILD, i.e. `stage0-sysroot` while this stage 1 test embeds a newer rustc_driver, and
    // the version check below cannot tell them apart (both print `1.99.0-dev`). So the
    // ambient values come LAST, after the local stage sysroots, as in the library's own
    // `compiler_sysroot`; TRUST_TEST_SYSROOT and TEST_SYSROOT stay explicit overrides.
    let env_sysroot = |key: &str| std::env::var_os(key).map(PathBuf::from);
    let mut candidates = ["TRUST_TEST_SYSROOT", "TEST_SYSROOT"]
        .into_iter()
        .filter_map(env_sysroot)
        .collect::<Vec<_>>();
    for host in
        ["host", "aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"]
    {
        for stage in ["stage2", "stage1"] {
            candidates.push(root.join("build").join(host).join(stage));
        }
    }
    candidates.extend(["RUSTC_SYSROOT", "SYSROOT"].into_iter().filter_map(env_sysroot));
    for candidate in candidates {
        let compiler = candidate.join("bin/trustc");
        if !compiler.is_file() {
            continue;
        }
        let has_std = candidate.join("lib/rustlib").read_dir().is_ok_and(|entries| {
            entries.flatten().any(|entry| {
                let names = entry
                    .path()
                    .join("lib")
                    .read_dir()
                    .map(|files| {
                        files
                            .flatten()
                            .map(|file| file.file_name().to_string_lossy().into_owned())
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                ["libcore-", "libstd-"].iter().all(|prefix| {
                    names.iter().any(|name| name.starts_with(prefix) && name.ends_with(".rmeta"))
                })
            })
        });
        if !has_std {
            continue;
        }
        if let Some(version) = rustc_interface::util::rustc_version_str() {
            let output = std::process::Command::new(compiler)
                .arg("--version")
                .output()
                .expect("query selected compiler identity");
            if !output.status.success()
                || !String::from_utf8_lossy(&output.stdout).contains(version.trim())
            {
                continue;
            }
        }
        return candidate
            .canonicalize()
            .expect("canonical compiler sysroot")
            .to_string_lossy()
            .into_owned();
    }
    panic!(
        "set TRUST_TEST_SYSROOT to the Trust sysroot matching this embedded rustc_driver (bin/trustc and host core/std metadata required)"
    );
}

/// Rustc's own answer for the tuple parameter, asked here, independently of the
/// extractor: `(size, align, field offsets by position)`.
type RustcLayout = (u64, u64, Vec<u64>);

struct Extracted {
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
    param_layout: Option<RustcLayout>,
}

#[derive(Default)]
struct LayoutCallbacks {
    bodies: BTreeMap<String, Extracted>,
}

impl rustc_driver::Callbacks for LayoutCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            let body = tcx.optimized_mir(did);
            let param = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
            let param_layout = (!param.has_non_region_param()).then(|| {
                let layout = tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(param))
                    .expect("a concrete tuple has a layout");
                (
                    layout.size.bytes(),
                    layout.align.bytes(),
                    (0..layout.fields.count()).map(|i| layout.fields.offset(i).bytes()).collect(),
                )
            });
            let logical = trust_mir_extract::extract_function(tcx, body);
            let faithful = trust_mir_extract::extract_function_faithful(tcx, body);
            self.bodies.insert(name, Extracted { logical, faithful, param_layout });
        }
        Compilation::Stop
    }
}

fn extract_fixture() -> BTreeMap<String, Extracted> {
    let mut callbacks = LayoutCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name=faithful_tuple_layouts_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
        "-Zinline-mir=no".into(),
        "-Cdebug-assertions=yes".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "the tuple-layout fixture must compile");
    assert_eq!(
        callbacks.bodies.keys().map(String::as_str).collect::<Vec<_>>(),
        ["generic_second", "pair_second", "triple_middle"]
    );
    callbacks.bodies
}

fn u(width: u32) -> Ty {
    Ty::Int { width, signed: false }
}

/// Run the lowered function on one aggregate argument and return its integer result.
fn run(module: &trust_ir::Module, fields: Vec<InterpretValue>) -> Result<u128, String> {
    let func = &module.functions[0];
    let param_ty = module
        .func_types
        .get(func.ty.as_usize())
        .and_then(|sig| sig.params.first())
        .cloned()
        .ok_or("the lowered function has no parameter")?;
    let arg = InterpretValue { ty: param_ty, kind: InterpretValueKind::Aggregate(fields) };
    let outcome = Interpreter::with_module(module)
        .execute_func(func.id, vec![arg])
        .map_err(|e| format!("{e:?}"))?;
    outcome
        .returns
        .first()
        .and_then(|v| v.as_int())
        .map(|i| i.as_unsigned())
        .ok_or_else(|| format!("no integer return: {:?}", outcome.returns))
}

fn int(ty: IrTy, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("in-range interpreter integer")
}

#[test]
fn the_faithful_lane_records_exactly_rustcs_tuple_layouts() {
    let bodies = extract_fixture();
    for (name, tuple) in [
        ("pair_second", Ty::Tuple(vec![u(32), u(8)])),
        ("triple_middle", Ty::Tuple(vec![u(8), u(32), u(16)])),
    ] {
        let extracted = &bodies[name];
        let (size, align, offsets) =
            extracted.param_layout.clone().expect("a concrete tuple parameter");
        let row = extracted.faithful.tuple_layouts.layout_of(&tuple).unwrap_or_else(|| {
            panic!("{name}: no row for {tuple:?} in {:?}", extracted.faithful.tuple_layouts)
        });
        assert_eq!(
            (row.size, row.align, &row.field_offsets),
            (size, align, &offsets),
            "{name}: the row must be rustc's own layout"
        );
        assert!(
            extracted.logical.tuple_layouts.is_empty(),
            "{name}: the logical (verifier) lane must carry no tuple layout: {:?}",
            extracted.logical.tuple_layouts
        );
    }
    // The reordering case is real: rustc does not keep `(u8, u32, u16)` in declaration
    // order, so a declaration-order rule would have named the wrong byte for `.1`.
    let (_, _, triple_offsets) = bodies["triple_middle"].param_layout.clone().expect("concrete");
    assert_ne!(triple_offsets, vec![0, 4, 8], "rustc reorders `(u8, u32, u16)`");
    // A tuple over a type parameter has no layout to ask for, and gets no row.
    let generic = &bodies["generic_second"].faithful.tuple_layouts;
    assert!(generic.is_empty(), "a generic tuple must carry no row: {generic:?}");
}

#[test]
fn a_faithful_tuple_field_address_executes_at_rustcs_offset() {
    let bodies = extract_fixture();

    let module = trust_ir_bridge::lower_to_trust_ir(&bodies["pair_second"].faithful)
        .expect("the faithful pair body lowers");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "invalid module: {errors:?}\n{module}");
    assert!(!module.tuple_layouts.is_empty(), "the row must reach the module\n{module}");
    assert_eq!(
        run(&module, vec![int(IrTy::U32, 0x1122_3344), int(IrTy::U8, 0x55)]),
        Ok(0x55),
        "{module}"
    );

    let module = trust_ir_bridge::lower_to_trust_ir(&bodies["triple_middle"].faithful)
        .expect("the faithful triple body lowers");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "invalid module: {errors:?}\n{module}");
    assert_eq!(
        run(
            &module,
            vec![int(IrTy::U8, 0x11), int(IrTy::U32, 0x2233_4455), int(IrTy::U16, 0x6677)]
        ),
        Ok(0x2233_4455),
        "{module}"
    );

    // The same bodies WITHOUT their rows (the pre-carrier input) name no offset, and
    // the interpreter refuses them: the rows, not something else, are what changed.
    let mut stripped = bodies["pair_second"].faithful.clone();
    stripped.tuple_layouts = Default::default();
    let module = trust_ir_bridge::lower_to_trust_ir(&stripped).expect("stripped body lowers");
    assert!(module.tuple_layouts.is_empty());
    let read = run(&module, vec![int(IrTy::U32, 0x1122_3344), int(IrTy::U8, 0x55)]);
    assert!(read.is_err(), "no row, no offset: the interpreter must refuse, got {read:?}");
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;
