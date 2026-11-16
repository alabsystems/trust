// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! ALLOC-STRIDE-ADT-2 (2026-10-07): the compiler's element-size side table, end to end.
//!
//! `extract_function_with_contract_bundle_and_elem_sizes` collects, beside the extracted
//! function, a lower bound of rustc's `size_of` per lowered type key. These rows compile
//! real Rust and check:
//!
//! * INVISIBILITY: the function extracted with the table is byte-identical to the one
//!   extracted without it — plain `serde_json`, the canonical hash material
//!   (`stable_model_json_bytes`) and `content_hash` — so no content, census or
//!   proof-certificate pin can move;
//! * the recorded bound of a pointer-heavy slice element (clean-ck0's shape: `Vec`,
//!   `String`, `Arc` fields and a recursive enum) is rustc's own `layout_of` size,
//!   asked here independently;
//! * a generic element and a zero-sized element record nothing usable.

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
use trust_types::{Ty, VerifiableFunction};

const FIXTURE_PATH: &str = "elem_size_table_fixture.rs";

const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]
use std::sync::Arc;

pub enum Expr {
    Var(u32),
    App(Box<Expr>, Box<Expr>),
    Lam(Arc<String>, Box<Expr>),
}

pub struct CtorInfo {
    pub name: String,
    pub n: u32,
    pub args: Vec<Expr>,
    pub tag: Arc<str>,
}

pub struct Zst;

pub fn ctor_src(s: &[CtorInfo]) -> usize {
    let v: Vec<Expr> = Vec::with_capacity(s.len());
    v.capacity()
}

pub fn pair_src(s: &[(String, Expr)]) -> usize {
    s.len()
}

pub fn vec_src(v: &Vec<CtorInfo>) -> usize {
    v.len()
}

pub fn generic_src<T>(s: &[T]) -> usize {
    s.len()
}

pub fn zst_src(s: &[Zst]) -> usize {
    s.len()
}

// clean-ck0's own shapes: `Name` and `Term` are recursive through `Arc`, and
// `Term` reaches `Name` through `TermKind`/`Level`/`LevelKind` — seven local ADTs deep.
pub struct Name(NameRepr);
pub enum NameRepr { Anonymous, Node(Arc<NameNode>) }
pub struct NameNode { parent: Name, component: Component }
pub enum Component { Str(Arc<str>), Num(u64) }
pub struct Level { kind: Arc<LevelKind> }
pub enum LevelKind { Zero, Succ(Level), Param(Name) }
pub struct ConstRef { name: Name, levels: Vec<Level> }
pub struct Term { kind: Arc<TermKind>, hash: u64, has_loose: bool }
pub enum TermKind { BVar(u32), Sort(Level), Const(ConstRef), App(Term, Term), Lam(Term, Term) }
pub struct CkCtorInfo { name: Name, num_fields: u32, field_tys: Vec<Term>, recursive: Vec<bool> }

pub fn ck_ctor_src(s: &[CkCtorInfo]) -> usize {
    s.len()
}

pub fn ck_name_term_src(s: &[(Name, Term)]) -> usize {
    s.len()
}

pub fn ck_term_src(s: &[Term]) -> usize {
    s.len()
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
            Err(io::Error::other("unexpected elem-size fixture path"))
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

struct Extracted {
    plain: VerifiableFunction,
    with_table: VerifiableFunction,
    table: trust_vcgen::ElemSizeTable,
    /// rustc's own `size_of` of parameter 1's element (a slice's or a `Vec`'s), asked
    /// here independently of the extractor; `None` when it is generic.
    elem_size: Option<u64>,
}

#[derive(Default)]
struct ElemCallbacks {
    bodies: BTreeMap<String, Extracted>,
}

impl rustc_driver::Callbacks for ElemCallbacks {
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
            let elem = match param.kind() {
                ty::Ref(_, inner, _) => match inner.kind() {
                    ty::Slice(elem) => Some(*elem),
                    ty::Adt(_, args) => args.types().next(),
                    _ => None,
                },
                _ => None,
            }
            .expect("parameter 1 is a slice or Vec reference");
            let elem_size = (!elem.has_non_region_param()).then(|| {
                tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(elem))
                    .expect("a concrete element has a layout")
                    .size
                    .bytes()
            });
            // Plain first, then with the table, then plain again: the scope must
            // leave nothing behind for a later extraction either.
            let plain = trust_mir_extract::extract_function_with_contract_bundle(tcx, body, None);
            let (with_table, table) =
                trust_mir_extract::extract_function_with_contract_bundle_and_elem_sizes(
                    tcx, body, None,
                );
            let again = trust_mir_extract::extract_function_with_contract_bundle(tcx, body, None);
            assert_eq!(
                serde_json::to_vec(&plain).expect("encode"),
                serde_json::to_vec(&again).expect("encode"),
                "{name}: extraction must be deterministic around the scope"
            );
            self.bodies.insert(name, Extracted { plain, with_table, table, elem_size });
        }
        Compilation::Stop
    }
}

fn extract_fixture(mir_opt_level: &str) -> BTreeMap<String, Extracted> {
    let mut callbacks = ElemCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name=elem_size_table_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        format!("-Zmir-opt-level={mir_opt_level}"),
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
    assert!(result.is_ok(), "the elem-size fixture must compile");
    assert_eq!(
        callbacks.bodies.keys().map(String::as_str).collect::<Vec<_>>(),
        [
            "ck_ctor_src",
            "ck_name_term_src",
            "ck_term_src",
            "ctor_src",
            "generic_src",
            "pair_src",
            "vec_src",
            "zst_src"
        ]
    );
    callbacks.bodies
}

/// The lowered element key of parameter 1 (`&[T]` or `&Vec<T>`).
fn elem_key(func: &VerifiableFunction) -> Ty {
    match &func.body.locals[1].ty {
        Ty::Ref { inner, .. } => match inner.as_ref() {
            Ty::Slice { elem } | Ty::Seq { elem, .. } => elem.as_ref().clone(),
            other => panic!("{}: parameter 1 points at {other:?}", func.def_path),
        },
        other => panic!("{}: parameter 1 is {other:?}", func.def_path),
    }
}

#[test]
fn the_table_never_changes_the_extracted_function() {
    for level in ["0", "2"] {
        for (name, e) in extract_fixture(level) {
            assert_eq!(
                serde_json::to_vec(&e.plain).expect("encode"),
                serde_json::to_vec(&e.with_table).expect("encode"),
                "{name} at mir-opt-level {level}: serde bytes moved"
            );
            assert_eq!(
                trust_types::stable_model_json_bytes(&e.plain.body).expect("hash material"),
                trust_types::stable_model_json_bytes(&e.with_table.body).expect("hash material"),
                "{name} at mir-opt-level {level}: hash material moved"
            );
            assert_eq!(
                e.plain.content_hash(),
                e.with_table.content_hash(),
                "{name} at mir-opt-level {level}: content hash moved"
            );
        }
    }
}

#[test]
fn a_concrete_pointer_heavy_element_records_rustcs_size_and_nothing_else_does() {
    let bodies = extract_fixture("0");
    for name in
        ["ctor_src", "pair_src", "vec_src", "ck_ctor_src", "ck_name_term_src", "ck_term_src"]
    {
        let e = &bodies[name];
        let size = e.elem_size.expect("a concrete element");
        assert!(size >= 24, "{name}: a pointer-heavy element is wider than 24 bytes: {size}");
        let key = elem_key(&e.with_table);
        // Every preimage of this key in this extraction is the element type itself,
        // so the minimum is rustc's exact size.
        assert_eq!(
            e.table.lower_bound(&key),
            Some(size),
            "{name}: key {key:?}\ntable ({} rows): {:?}",
            e.table.len(),
            e.table
        );
    }
    // A generic element: no layout, so no usable row.
    let generic = &bodies["generic_src"];
    assert_eq!(generic.elem_size, None);
    assert_eq!(generic.table.lower_bound(&elem_key(&generic.with_table)), None);
    // A zero-sized element: no stride.
    let zst = &bodies["zst_src"];
    assert_eq!(zst.elem_size, Some(0));
    assert_eq!(zst.table.lower_bound(&elem_key(&zst.with_table)), None);
}

// ---------------------------------------------------------------------------
// Review 2026-10-07: Lever A's field compaction (`compact_oversized_field`) mints
// an erased-name marker AFTER the recorded lowering exit. That key is shared with a
// same-named local cut point (bin `foo` depending on lib `foo`, the default Cargo
// layout) and with other instantiations of a generic, so the compacted preimage
// must be recorded under it, or the marker reads another type's (larger) row.
// ---------------------------------------------------------------------------

/// `pub struct S` with 130 `u8` fields: 130 bytes, and 131 lowered nodes, over
/// `MAX_DATATYPE_FIELD_NODES` (128), so as a field it is compacted (given a user
/// `Drop`, below).
fn wide_u8_fields(prefix: &str, n: usize) -> String {
    (0..n).map(|i| format!("{prefix}f{i}: u8, ")).collect()
}

fn same_name_lib_source() -> String {
    // The user `Drop` withholds the drop-total stamp, which would otherwise exempt the
    // field from compaction (`tcx_drop_is_total`; the F6 exemption in the struct arm).
    format!(
        "pub struct S {{ {} }}\nimpl Drop for S {{ fn drop(&mut self) {{}} }}\n",
        wide_u8_fields("pub ", 130)
    )
}

fn same_name_bin_source() -> String {
    format!(
        r#"#![allow(dead_code)]
// A LOCAL recursive `S`: a canonical cut point whose marker spells `foo::S`.
struct S {{ next: Option<Box<S>>, pad: [u64; 32] }}
// The dependency's same-named `foo::S` (130 bytes), compacted as a field.
struct Holder {{ s: ::foo::S }}
fn f(src: &[Holder], _w: &[S]) -> usize {{ src.len() }}

// Two instantiations of one generic, both compacted under ONE erased marker.
struct Big<T> {{ t: T, {} }}
impl<T> Drop for Big<T> {{ fn drop(&mut self) {{}} }}
struct H1 {{ b: Big<u8> }}
struct H2 {{ b: Big<[u64; 64]> }}
fn g(a: &[H2], b: &[H1]) -> usize {{ a.len() + b.len() }}

fn main() {{}}
"#,
        wide_u8_fields("", 130)
    )
}

#[derive(Default)]
struct SameNameCallbacks {
    bodies: BTreeMap<String, (VerifiableFunction, trust_vcgen::ElemSizeTable)>,
}

impl rustc_driver::Callbacks for SameNameCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            if name == "main" {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let (func, table) =
                trust_mir_extract::extract_function_with_contract_bundle_and_elem_sizes(
                    tcx, body, None,
                );
            self.bodies.insert(name, (func, table));
        }
        Compilation::Stop
    }
}

struct NoopCallbacks;
impl rustc_driver::Callbacks for NoopCallbacks {}

fn run_rustc(args: Vec<String>, callbacks: &mut (dyn rustc_driver::Callbacks + Send)) {
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "fixture must compile: {args:?}");
}

fn extract_same_name_fixture() -> BTreeMap<String, (VerifiableFunction, trust_vcgen::ElemSizeTable)>
{
    let dir = option_env!("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join(format!("elem_size_same_name_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let lib = dir.join("lib.rs");
    let bin = dir.join("main.rs");
    std::fs::write(&lib, same_name_lib_source()).expect("write lib");
    std::fs::write(&bin, same_name_bin_source()).expect("write bin");
    let sysroot = compiler_sysroot();
    run_rustc(
        vec![
            "rustc".into(),
            lib.to_string_lossy().into_owned(),
            "--crate-name=foo".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "--emit=metadata".into(),
            "-Cmetadata=lib".into(),
            "-Zcodegen-backend=dummy".into(),
            "--out-dir".into(),
            dir.to_string_lossy().into_owned(),
            "--sysroot".into(),
            sysroot.clone(),
        ],
        &mut NoopCallbacks,
    );
    let mut callbacks = SameNameCallbacks::default();
    run_rustc(
        vec![
            "rustc".into(),
            bin.to_string_lossy().into_owned(),
            "--crate-name=foo".into(),
            "--crate-type=bin".into(),
            "--edition=2021".into(),
            "-Cmetadata=bin".into(),
            "--extern".into(),
            format!("foo={}", dir.join("libfoo.rmeta").display()),
            "-Zmir-opt-level=0".into(),
            "-Zinline-mir=no".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            "--sysroot".into(),
            sysroot,
        ],
        &mut callbacks,
    );
    let _ = std::fs::remove_dir_all(&dir);
    callbacks.bodies
}

/// The lowered element of parameter `index` (`&[T]`).
fn slice_elem(func: &VerifiableFunction, index: usize) -> Ty {
    match &func.body.locals[index].ty {
        Ty::Ref { inner, .. } => match inner.as_ref() {
            Ty::Slice { elem } => elem.as_ref().clone(),
            other => panic!("{}: parameter {index} points at {other:?}", func.def_path),
        },
        other => panic!("{}: parameter {index} is {other:?}", func.def_path),
    }
}

/// The single field type of a lowered one-field struct.
fn only_field(ty: &Ty) -> Ty {
    match ty {
        Ty::Adt { fields, .. } if fields.len() == 1 => fields[0].1.clone(),
        other => panic!("expected a one-field struct, got {other:?}"),
    }
}

fn is_marker(ty: &Ty) -> bool {
    matches!(ty, Ty::Datatype { variants, .. } if variants.is_empty())
}

#[test]
fn a_compacted_field_records_its_preimage_under_the_shared_marker() {
    let bodies = extract_same_name_fixture();

    // (1) bin `foo` / lib `foo`: `Holder.s` is compacted to the SAME key as the
    // local cut point `S` (264 bytes). Before the fix the key's row was the local
    // `S`'s 264 alone, so `Holder` (130 bytes) read a 264-byte stride.
    let (f, table) = &bodies["f"];
    let compacted = only_field(&slice_elem(f, 1));
    assert!(is_marker(&compacted), "Holder.s must be compacted: {compacted:?}");
    let local_s = slice_elem(f, 2);
    assert_eq!(
        compacted, local_s,
        "the fixture must exercise the collision: compacted dependency `S` and local cut point `S` share one key"
    );
    assert_eq!(
        table.lower_bound(&compacted),
        Some(130),
        "the shared marker's row must be the MINIMUM over both preimages (lib S = 130, local S = 264)"
    );
    assert_eq!(table.lower_bound(&slice_elem(f, 1)), Some(130), "Holder itself is 130 bytes");

    // (2) Two instantiations of one generic, each compacted under ONE erased marker:
    // both preimages are recorded, so the row is the smaller one (Big<u8> = 131).
    let (g, table) = &bodies["g"];
    let wide = only_field(&slice_elem(g, 1));
    let narrow = only_field(&slice_elem(g, 2));
    assert!(is_marker(&wide) && is_marker(&narrow), "both Big fields compacted");
    assert_eq!(wide, narrow, "erased generic markers share one key");
    assert_eq!(
        table.lower_bound(&wide),
        Some(131),
        "Big<[u64; 64]> (642) and Big<u8> (131) min-merge to 131"
    );
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;
