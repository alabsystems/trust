// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Trust (F3 review, rounds 3-4, 2026-09-30): the storage rule the derived-MIR differential
//! applies to the REAL derived body, EXECUTED in process on bodies the compiler built.
//!
//! `trust_thir_lower::mir_differential::compare_derived` extracts built and derived MIR into the
//! verifier's model before comparing them, and that extraction keeps an `Assert` message's kind
//! but drops its operands, so neither the canonical channel nor the exact marker channel can see
//! them. What reads them is `mir_storage_dead_use` -- rustc's `-Zlint-mir` storage rule over the
//! derived `mir::Body` -- which clears `markers_exact` on a use of a local whose storage may be
//! dead. This test runs that rule (`trust_thir_lower::to_mir::derived_mir_storage_dead_use`) on
//! the real `optimized_mir` of `a + 1 + 2` and `a + 1`, compiled in process with
//! `-Zmir-opt-level=0` so the storage markers and the overflow asserts survive, before and after
//! planting one storage-dead message operand.
//!
//! WHY NOT THROUGH `compare_derived` HERE: an embedded `rustc_driver::run_compiler` frontend is
//! `EmbeddedNoOfficialEvidence` and refuses `-Ztrust-ir-lower` outright, so no in-process test can
//! reach the differential. Through the driver binary, the tracked
//! `-Ztrust-test-mutate-derived-assert-msg` plants the same operand in the producer's derived body,
//! but the driver fences it off every `-Ztrust-dump` sink, so `compare_derived`'s verdict on that
//! body is written nowhere; `tests/run-make/trust-ir-derived-assert-msg-storage-rule` pins the
//! fence and the plant. The call of this rule inside `compare_derived` is pinned token for token
//! by the frozen file's refinement census.

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
use rustc_middle::mir::{self, AssertKind, Local, Operand, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

const FIXTURE_PATH: &str = "chain.rs";

/// `chain2` has two checked adds: built retires the parameter's operand temp (`StorageDead`) in
/// the block that ends in the SECOND overflow assert, whose message then reads a live `u64`.
/// `chain1` has one checked add and retires nothing before its assert.
const FIXTURE_SOURCE: &str = r#"
pub fn chain2(a: u64) -> u64 {
    a + 1 + 2
}

pub fn chain1(a: u64) -> u64 {
    a + 1
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
            Err(io::Error::other("unexpected derived-assert-msg fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported for this fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

/// The same explicit sysroot overrides as `producer_lowering_gaps.rs`, and the same refusal of a
/// proven driver version mismatch.
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

/// What the storage rule said about one compiler-built body, before and after the plant.
#[derive(Debug, Default)]
struct Finding {
    unmutated: Option<String>,
    /// `(block, from, to)`: the overflow-assert message operand repointed from `_from` to a
    /// same-typed `_to` the same block has already retired.
    planted: Option<(usize, usize, usize)>,
    mutated: Option<String>,
    /// The same operand repointed to the argument `_1` instead: a live local, so a control.
    live_control: Option<String>,
}

#[derive(Default)]
struct Probe {
    findings: BTreeMap<String, Finding>,
}

/// The FIRST overflow-assert message operand (a bare local) for which the same block has already
/// retired (`StorageDead`, not revived) a different local of the same type: repoint it there.
fn plant(body: &mut mir::Body<'_>) -> Option<(usize, usize, usize)> {
    let tys: Vec<_> = body.local_decls.iter().map(|decl| decl.ty).collect();
    for (bb, data) in body.basic_blocks_mut().iter_enumerated_mut() {
        let mut retired: Vec<Local> = Vec::new();
        for statement in &data.statements {
            match statement.kind {
                StatementKind::StorageDead(local) => retired.push(local),
                StatementKind::StorageLive(local) => retired.retain(|dead| *dead != local),
                _ => {}
            }
        }
        let Some(terminator) = data.terminator.as_mut() else { continue };
        let TerminatorKind::Assert { msg, .. } = &mut terminator.kind else { continue };
        let AssertKind::Overflow(_, lhs, rhs) = &mut **msg else { continue };
        for operand in [lhs, rhs] {
            let (Operand::Copy(place) | Operand::Move(place)) = operand else { continue };
            if !place.projection.is_empty() {
                continue;
            }
            let from = place.local;
            if let Some(&to) = retired
                .iter()
                .find(|dead| **dead != from && tys[dead.as_usize()] == tys[from.as_usize()])
            {
                place.local = to;
                return Some((bb.as_usize(), from.as_usize(), to.as_usize()));
            }
        }
    }
    None
}

/// Repoint the operand `plant` moved to the argument `_1` instead (always live).
fn repoint_to_argument(body: &mut mir::Body<'_>, block: usize, to: usize) {
    let data = &mut body.basic_blocks_mut()[mir::BasicBlock::from_usize(block)];
    let terminator = data.terminator.as_mut().expect("the planted block keeps its assert");
    let TerminatorKind::Assert { msg, .. } = &mut terminator.kind else {
        panic!("the planted block keeps its assert")
    };
    let AssertKind::Overflow(_, lhs, rhs) = &mut **msg else { panic!("an overflow assert") };
    for operand in [lhs, rhs] {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if place.local.as_usize() == to {
                place.local = Local::from_usize(1);
            }
        }
    }
}

impl rustc_driver::Callbacks for Probe {
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
            let body = tcx.optimized_mir(did).clone();
            let mut finding = Finding {
                unmutated: trust_thir_lower::to_mir::derived_mir_storage_dead_use(&body),
                ..Finding::default()
            };
            let mut mutated = body.clone();
            finding.planted = plant(&mut mutated);
            if let Some((block, _, to)) = finding.planted {
                finding.mutated = trust_thir_lower::to_mir::derived_mir_storage_dead_use(&mutated);
                let mut control = mutated.clone();
                repoint_to_argument(&mut control, block, to);
                finding.live_control =
                    trust_thir_lower::to_mir::derived_mir_storage_dead_use(&control);
            }
            self.findings.insert(tcx.item_name(did).to_string(), finding);
        }
        Compilation::Stop
    }
}

#[test]
fn the_storage_rule_clears_markers_exact_on_a_planted_dead_message_operand() {
    let args = vec![
        "rustc".to_string(),
        FIXTURE_PATH.to_string(),
        "--crate-name=chain".to_string(),
        "--crate-type=lib".to_string(),
        "--edition=2021".to_string(),
        "-Copt-level=0".to_string(),
        // RemoveStorageMarkers is enabled only at mir-opt-level > 0: keep the markers.
        "-Zmir-opt-level=0".to_string(),
        "-Coverflow-checks=on".to_string(),
        "-Zno-codegen".to_string(),
        "-Zcodegen-backend=dummy".to_string(),
        "--sysroot".to_string(),
        compiler_sysroot(),
    ];
    let mut probe = Probe::default();
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut probe);
        Ok(())
    });
    assert!(result.is_ok(), "the fixture must compile");

    // chain2: the rule passes the body as built; a planted storage-dead message operand is
    // exactly what it reports, at the planted block and local; the same operand repointed to a
    // live local is not reported. The extraction `compare_derived` compares drops message
    // operands (`trust_mir_extract::convert` maps `AssertKind::Overflow(op, _, _)` to
    // `AssertMessage::Overflow(op)`), so this rule is the only check that sees the plant.
    let chain2 = probe.findings.get("chain2").expect("chain2 was compiled");
    assert_eq!(chain2.unmutated, None, "the compiler-built body passes the storage rule");
    let (block, from, to) = chain2
        .planted
        .expect("chain2's second overflow assert follows a same-typed StorageDead in its block");
    assert_ne!(from, to);
    assert_eq!(
        chain2.mutated.as_deref(),
        Some(format!("use of _{to} in bb{block} while its storage may be dead").as_str()),
        "the storage rule must report the planted dead message operand, and only it"
    );
    assert_eq!(chain2.live_control, None, "a live message operand is not a storage-dead use");

    // chain1: one checked add, nothing retired before its assert, nothing to plant.
    let chain1 = probe.findings.get("chain1").expect("chain1 was compiled");
    assert_eq!(chain1.unmutated, None);
    assert_eq!(chain1.planted, None, "chain1 retires nothing before its assert");
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;
