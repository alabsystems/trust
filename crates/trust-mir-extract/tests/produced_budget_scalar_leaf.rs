// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A scalar field keeps its type when the fields declared before it spend the
//! produced-node budget (TRUST-KI-1014-1, 2026-10-14).
//!
//! `MAX_TYPE_LOWERING_PRODUCED_NODES` (8000) is metered over a whole walk, so a type
//! lowered after the budget is spent degrades to the fail-closed `Unsupported` leaf.
//! Before this fix that held for scalars too: in `struct Late { big: T4, grace: u32 }`
//! the walk spent the budget inside `big` (a tuple tower of 11,111 nodes) and `grace`
//! lowered to `Unsupported`. `self.grace -= 1` then failed trust-vcgen's admission
//! ("CheckedBinaryOp lhs must match the tuple payload's supported fixed-width integer
//! type"), and the whole body became one `MalformedTrustIr` row. Measured on aterm-wasm
//! (`AtermTerminal::reflow_grace`, the channel seal `b58a105dde`): the decrement's
//! overflow obligation and its hardened twin, proved when the field comes first, were
//! lost. `tests/ui/trust/produced_budget_scalar_field_after_fat_sibling.rs` pins the
//! verdict end to end; this file pins the extracted types:
//!
//! * `grace` is `u32` in `Late` (declared after the fat field) exactly as in `Early`
//!   (declared before it), and the decrement passes VC-generation admission;
//! * the budget still bites: `Late`'s walk DID cross it, and the non-scalar `tail`
//!   declared after `grace` is still the fail-closed degraded leaf.

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
use rustc_middle::ty::TyCtxt;
use trust_types::{BinOp, Ty, VcKind, VerifiableFunction};

const FIXTURE_PATH: &str = "produced_budget_scalar_leaf_fixture.rs";

const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

// T1 is 11 produced nodes, T2 111, T3 1111, T4 11111: lowering T4 alone crosses the
// 8000-node produced budget of the walk that reaches it.
type T1 = (u64, u64, u64, u64, u64, u64, u64, u64, u64, u64);
type T2 = (T1, T1, T1, T1, T1, T1, T1, T1, T1, T1);
type T3 = (T2, T2, T2, T2, T2, T2, T2, T2, T2, T2);
type T4 = (T3, T3, T3, T3, T3, T3, T3, T3, T3, T3);

pub struct Late {
    pub big: T4,
    pub grace: u32,
    pub tail: (u8, u16),
}

impl Late {
    pub fn tick(&mut self) {
        if self.grace > 0 {
            self.grace -= 1;
        }
    }
}

pub struct Early {
    pub grace: u32,
    pub big: T4,
}

impl Early {
    pub fn tick(&mut self) {
        if self.grace > 0 {
            self.grace -= 1;
        }
    }
}
"#;

const DEGRADED_DETAIL: &str =
    "recursive ADT (degraded: type lowering exceeded produced-node budget)";

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected produced-budget fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in this fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

// The same explicit sysroot overrides and driver-version refusal as
// `faithful_tuple_layouts.rs` (an integration target cannot call the library's private
// cfg(test) helper).
fn compiler_sysroot() -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
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

#[derive(Default)]
struct ExtractCallbacks {
    /// `<Self type>::tick` -> the logical (verifier) extraction of its body.
    bodies: BTreeMap<String, VerifiableFunction>,
}

impl rustc_driver::Callbacks for ExtractCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::AssocFn) {
                continue;
            }
            let Some(impl_did) = tcx.impl_of_assoc(did) else { continue };
            let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
            let Some(adt) = self_ty.ty_adt_def() else { continue };
            let key = format!("{}::{}", tcx.item_name(adt.did()), tcx.item_name(did));
            let body = tcx.optimized_mir(did);
            self.bodies.insert(key, trust_mir_extract::extract_function(tcx, body));
        }
        Compilation::Stop
    }
}

fn extract_fixture() -> BTreeMap<String, VerifiableFunction> {
    let mut callbacks = ExtractCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name=produced_budget_scalar_leaf_fixture".into(),
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
    assert!(result.is_ok(), "the produced-budget fixture must compile");
    assert_eq!(
        callbacks.bodies.keys().map(String::as_str).collect::<Vec<_>>(),
        ["Early::tick", "Late::tick"]
    );
    callbacks.bodies
}

/// The fields of `self`'s struct, as the extractor lowered `_1: &mut Self`.
fn self_fields(func: &VerifiableFunction) -> Vec<(String, Ty)> {
    let decl = func
        .body
        .locals
        .iter()
        .find(|decl| decl.index == 1)
        .unwrap_or_else(|| panic!("{}: no local _1", func.name));
    match &decl.ty {
        Ty::Ref { mutable: true, inner } => match inner.as_ref() {
            Ty::Adt { fields, .. } => fields.iter().cloned().collect(),
            other => panic!("{}: `*self` is not a lowered struct: {other:?}", func.name),
        },
        other => panic!("{}: `self` is not `&mut`: {other:?}", func.name),
    }
}

fn field<'a>(fields: &'a [(String, Ty)], name: &str) -> &'a Ty {
    &fields
        .iter()
        .find(|(field, _)| field == name)
        .unwrap_or_else(|| panic!("no field `{name}` in {fields:?}"))
        .1
}

fn is_degraded_leaf(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Unsupported { kind, detail } if kind == "TyKind::Adt" && detail == DEGRADED_DETAIL
    )
}

#[test]
fn a_scalar_field_after_a_fat_sibling_keeps_its_type() {
    let bodies = extract_fixture();
    let u32_ty = Ty::Int { width: 32, signed: false };

    let early = self_fields(&bodies["Early::tick"]);
    assert_eq!(field(&early, "grace"), &u32_ty, "control: `grace` declared first");

    let late = self_fields(&bodies["Late::tick"]);
    assert_eq!(
        field(&late, "grace"),
        &u32_ty,
        "`grace` declared after the fat field must lower exactly as when declared first: {late:?}"
    );
    // The budget still bites: the walk crossed it, and a non-scalar lowered after that
    // point is still the fail-closed degraded leaf.
    assert!(
        is_degraded_leaf(field(&late, "tail")),
        "`tail` must still degrade once the walk's budget is spent: {late:?}"
    );
}

#[test]
fn the_decrement_passes_vcgen_admission_and_owes_its_overflow_row() {
    let bodies = extract_fixture();
    for name in ["Early::tick", "Late::tick"] {
        let vcs = trust_vcgen::try_generate_vcs(&bodies[name]).unwrap_or_else(|error| {
            panic!("{name}: the decrement must pass VC-generation admission: {error}")
        });
        assert!(
            vcs.iter()
                .any(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })),
            "{name}: the `-= 1` overflow obligation must be generated: {:?}",
            vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;
