// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! ARGS-FINGERPRINT-READ-1 round 4 (2026-10-08): the duplicate-crate-name tag on a
//! call's generic arguments covers a LOCAL type whose crate name an extern shares.
//!
//! Cargo's bin+lib layout compiles a package's bin against its own lib, and both carry
//! the package's crate name. The display printer stamps no crate identity inside generic
//! arguments, so the bin's own `foo::T` and the lib's `foo::T` print alike, and a call
//! naming either is not identified by its display. `generic_args_name_an_unauthenticated_crate`
//! (convert.rs) must therefore tag a call whose arguments name the LOCAL crate's types
//! when an extern shares its name. Round 2 masked the local crate out (`!is_local`);
//! round 3 restored it (`|| (is_local && name_is_shared)`), but no test saw the tag
//! directly: the UI pin `binlib_same_name_generic.rs` stays green with the round-2
//! mask restored, because round 3's `DefId` self-call gate withdraws the same row
//! (review of round 3, 2026-10-08). These rows read the extracted callee spelling
//! itself, so reverting the local arm turns them red (measured 2026-10-08 with the round-2
//! mask restored: the first test fails on `foo::id::<foo::T>`, untagged).
//!
//! Controls: a call whose only argument is a primitive stays untagged (the tag is not
//! on every generic call of a duplicate-name graph), and the same local call in a crate
//! whose name nothing shares stays untagged.
//!
//! ROUND 5 (2026-10-08, review of round 3 item i: "a pin for (B) where (A)'s `DefId`
//! gate does not already decline"). The tag is a VERDICT input wherever no compiler
//! frame carries the `DefId` self-call set: trust-vcgen's public `generate_vcs` called
//! with no context (the trust-clean regenerations, KNOWN_HAZARDS) compares rendered
//! paths alone, and only the tag keeps the call into the sibling impl from reading as a
//! self call. `the_tag_alone_withholds_the_descent_row_without_compiler_context` runs
//! vcgen exactly so on the extracted body: with the tag, no recursion row; with the tag
//! stripped from the same body (what the round-2 mask produced), the inferred lane mints
//! the "recursion measure `n` may not decrease" descent row for a call that never runs
//! this body. Reverting (B) alone turns that test red (measured, round-5 commit).

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

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use trust_types::{Terminator, VerifiableFunction};

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

const LIB_SOURCE: &str = "pub struct T;\n";

/// The bin of the pair (here a lib crate type, so nothing needs a `main`): a local
/// `T` named like the lib's, a generic free function, and the round-3 shape (a call
/// into a sibling impl whose self type names the local `T`).
const BIN_SOURCE: &str = r#"
#![allow(dead_code)]
pub struct T;
pub struct W<X>(pub X);
pub trait Tr {
    fn f<G: Copy>(n: u64, g: G) -> u64;
}
pub fn id<G>(g: G) -> G {
    g
}
pub fn names_local_t() -> T {
    id::<T>(T)
}
pub fn names_only_u8() -> u8 {
    id::<u8>(1)
}
impl Tr for W<other::T> {
    fn f<G: Copy>(n: u64, g: G) -> u64 {
        if n == 0 {
            return 0;
        }
        <W<T> as Tr>::f::<G>(n - 1, g)
    }
}
impl Tr for W<T> {
    fn f<G: Copy>(n: u64, _g: G) -> u64 {
        n
    }
}
"#;

#[derive(Default)]
struct CallCallbacks {
    /// Every extracted local function body, by item name, with its call spellings.
    calls: BTreeMap<String, Vec<Vec<String>>>,
    /// Every extracted local function body, by item name.
    functions: BTreeMap<String, Vec<VerifiableFunction>>,
}

impl rustc_driver::Callbacks for CallCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(
                tcx.def_kind(did),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            ) {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let func = trust_mir_extract::extract_function_with_contract_bundle(tcx, body, None);
            let name = tcx.item_name(did).to_string();
            self.calls.entry(name.clone()).or_default().push(call_names(&func));
            self.functions.entry(name).or_default().push(func);
        }
        Compilation::Stop
    }
}

fn call_names(func: &VerifiableFunction) -> Vec<String> {
    func.body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func, .. } => Some(func.clone()),
            _ => None,
        })
        .collect()
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

/// Compile the lib as `other_name`, then the bin as `bin_name` against it (`--extern
/// other=`), and return the bin's call spellings.
fn extract_bin(other_name: &str, bin_name: &str) -> BTreeMap<String, Vec<Vec<String>>> {
    extract_bin_callbacks(other_name, bin_name).calls
}

/// Each fixture compile gets a directory of its own (see extract_bin_callbacks).
static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// [`extract_bin`], returning the extracted bodies too.
fn extract_bin_callbacks(other_name: &str, bin_name: &str) -> CallCallbacks {
    let dir = option_env!("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join(format!(
            "args_tag_local_{other_name}_{bin_name}_{}_{}",
            std::process::id(),
            // Two tests of this binary compile `("foo", "foo")` at once: without a
            // per-call component they shared one directory, and the first to finish
            // removed the other's lib.rs mid-compile.
            FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let lib = dir.join("lib.rs");
    let bin = dir.join("bin.rs");
    std::fs::write(&lib, LIB_SOURCE).expect("write lib");
    std::fs::write(&bin, BIN_SOURCE).expect("write bin");
    let sysroot = compiler_sysroot();
    run_rustc(
        vec![
            "rustc".into(),
            lib.to_string_lossy().into_owned(),
            format!("--crate-name={other_name}"),
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
    let mut callbacks = CallCallbacks::default();
    run_rustc(
        vec![
            "rustc".into(),
            bin.to_string_lossy().into_owned(),
            format!("--crate-name={bin_name}"),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Cmetadata=bin".into(),
            "--extern".into(),
            format!("other={}", dir.join(format!("lib{other_name}.rmeta")).display()),
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
    callbacks
}

/// The one call of the single body named `name` whose spelling contains `needle`.
fn only_call<'a>(
    calls: &'a BTreeMap<String, Vec<Vec<String>>>,
    name: &str,
    needle: &str,
) -> &'a str {
    let found: Vec<&str> = calls
        .get(name)
        .unwrap_or_else(|| panic!("no body named {name}: {calls:?}"))
        .iter()
        .flatten()
        .filter(|call| call.contains(needle))
        .map(String::as_str)
        .collect();
    assert_eq!(found.len(), 1, "{name}: calls containing {needle:?}: {found:?}");
    found[0]
}

#[test]
fn a_local_type_is_tagged_when_an_extern_shares_the_crate_name() {
    let calls = extract_bin("foo", "foo");
    let local = only_call(&calls, "names_local_t", "id");
    assert!(
        trust_types::args_display_may_name_a_same_named_crate(local),
        "`id::<T>` names the LOCAL `foo::T`, and the lib `foo` prints its `T` alike: {local}"
    );
    // The round-3 shape: from inside `impl Tr for W<other::T>`, the call into the
    // sibling `impl Tr for W<T>` (both bodies render one def path). Exactly one of the two
    // `f` bodies has a call into `Tr::f`.
    let into_sibling = only_call(&calls, "f", "as foo::Tr>::f");
    assert!(
        trust_types::args_display_may_name_a_same_named_crate(into_sibling),
        "the call into the sibling impl names the LOCAL `foo::T` in `Self`: {into_sibling}"
    );
    let primitive = only_call(&calls, "names_only_u8", "id");
    assert!(
        !trust_types::args_display_may_name_a_same_named_crate(primitive),
        "a primitive argument names no crate: {primitive}"
    );
}

#[test]
fn a_local_type_is_untagged_when_no_crate_shares_its_name() {
    let calls = extract_bin("foolib", "foo");
    let local = only_call(&calls, "names_local_t", "id");
    assert!(
        !trust_types::args_display_may_name_a_same_named_crate(local),
        "no other crate is named `foo`, so `foo::T` identifies the local type: {local}"
    );
    let into_sibling = only_call(&calls, "f", "as foo::Tr>::f");
    assert!(!trust_types::args_display_may_name_a_same_named_crate(into_sibling), "{into_sibling}");
}

/// trust-vcgen's direct-self "recursion measure ... may not decrease" rows, generated
/// with NO compiler context (no `VcgenContext` frame, so no `DefId` self-call set).
fn unframed_recursion_rows(func: &VerifiableFunction) -> usize {
    trust_vcgen::generate_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, trust_types::VcKind::NonTermination { context, .. }
                if context == trust_vcgen::RECURSION_TERMINATION_CONTEXT)
        })
        .count()
}

#[test]
fn the_tag_alone_withholds_the_descent_row_without_compiler_context() {
    let extracted = extract_bin_callbacks("foo", "foo");
    // The `f` of `impl Tr for W<other::T>`: the one body named `f` with a call into
    // `Tr::f` (the sibling `impl Tr for W<T>` renders the SAME def path).
    let callers: Vec<&VerifiableFunction> = extracted.functions["f"]
        .iter()
        .filter(|func| call_names(func).iter().any(|call| call.contains("as foo::Tr>::f")))
        .collect();
    assert_eq!(callers.len(), 1, "exactly one `f` calls into the sibling impl");
    let caller = callers[0];
    let call = call_names(caller).into_iter().find(|call| call.contains("as foo::Tr>::f")).unwrap();
    assert_eq!(
        unframed_recursion_rows(caller),
        0,
        "with no compiler context only the tag keeps `{call}` from reading as a self call \
         of `{}`",
        caller.def_path
    );
    // The verdict above is asserted FIRST, so a revert of (B) fails on the descent row
    // itself, not only on the spelling; the tag is then checked directly.
    assert!(
        trust_types::args_display_may_name_a_same_named_crate(&call),
        "(B): the call into the sibling impl is tagged: {call}"
    );
    // Control: the same body with the tag stripped (the round-2 producer's output) DOES
    // read the call as a self call and mints the descent row, so the zero above is the
    // tag's doing, not the fixture's.
    let mut untagged = caller.clone();
    for block in &mut untagged.body.blocks {
        if let Terminator::Call { func, .. } = &mut block.terminator {
            *func = trust_types::strip_trailing_args_fingerprint(func).to_string();
        }
    }
    assert!(
        unframed_recursion_rows(&untagged) > 0,
        "control: the untagged spelling must mint the false descent row on `{}`",
        caller.def_path
    );
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;
