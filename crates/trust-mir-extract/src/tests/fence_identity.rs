// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! FENCE-IDENTITY-1: the standard fences are recognized by compiler identity,
//! not by a rendered path ending in `::fence`/`::compiler_fence`. Exercised on
//! real compiler MIR: user callees spelled `fence`/`compiler_fence` (a method
//! and a free function each) stay plain calls, and the real
//! `std::sync::atomic::{fence, compiler_fence}` stay atomic fences.

use trust_types::AtomicOpKind;

use super::*;
use crate::convert::{AtomicCalleeIdentity, SysrootFence, atomic_callee_identity};

const FIXTURE_PATH: &str = "fence_identity_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]
use std::sync::atomic::{compiler_fence as real_compiler_fence, fence as real_fence, Ordering};

pub struct B { pub n: u64 }
impl B {
    #[inline(never)]
    pub fn fence(&mut self, o: u8) { self.n = self.n.wrapping_add(o as u64); }
    #[inline(never)]
    pub fn compiler_fence(&mut self, o: u8) { self.n = self.n.wrapping_add(o as u64); }
}

// The dangerous shape: a lone integer argument in 0..=4 IS a valid ordering
// discriminant, so the old suffix rule parsed these as real fences.
#[inline(never)]
pub fn fence(o: u8) -> u8 { o.wrapping_add(1) }
#[inline(never)]
pub fn compiler_fence(o: u8) -> u8 { o.wrapping_add(1) }

pub fn user_method_fences(b: &mut B) {
    b.fence(4);
    b.compiler_fence(2);
}
pub fn user_free_fences() -> u8 {
    fence(4).wrapping_add(compiler_fence(2))
}
pub fn real_fences() {
    real_fence(Ordering::SeqCst);
    real_compiler_fence(Ordering::Acquire);
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
            Err(io::Error::other("unexpected fence fixture source path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported in fence fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct FenceCallbacks {
    user_calls: usize,
    real_fences: Vec<String>,
}

impl rustc_driver::Callbacks for FenceCallbacks {
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
            let caller = tcx.item_name(did).to_string();
            let real = match caller.as_str() {
                "user_method_fences" | "user_free_fences" => false,
                "real_fences" => true,
                _ => continue,
            };
            let body = tcx.optimized_mir(did);
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    continue;
                };
                let Some((callee, _)) = func.const_fn_def() else { continue };
                let leaf = tcx.item_name(callee).to_string();
                if leaf != "fence" && leaf != "compiler_fence" {
                    continue;
                }
                let identity = atomic_callee_identity(tcx, func);
                let converted = crate::convert::convert_basic_block(
                    tcx,
                    bb,
                    data,
                    Some(body),
                    Some(body.typing_env(tcx)),
                    Some(body.source.def_id()),
                    crate::convert::OptionalOverflowAssertCodegen::ThisSession,
                );
                if real {
                    let expected = if leaf == "fence" {
                        SysrootFence::Fence
                    } else {
                        SysrootFence::CompilerFence
                    };
                    assert_eq!(identity.fence(), Some(expected), "{caller}: real {leaf} identity");
                    // The identity reaches the ordering parser. At this opt level the
                    // argument is a typed `Ordering` enum constant, which
                    // `ordering_from_args` (integer constants only) does not decode, so
                    // the site stays FAIL-CLOSED as an opaque `UnsupportedAtomicMetadata`
                    // — on `main` before this change too. Optimized MIR inlines the
                    // wrapper into the const-generic `atomic_fence` intrinsic (Form A).
                    // Either outcome is accepted; a plain Call with no metadata is not.
                    let outcome = match &converted.terminator {
                        Terminator::Call { atomic: Some(atomic), .. } => {
                            assert_eq!(
                                atomic.op_kind,
                                if leaf == "fence" {
                                    AtomicOpKind::Fence
                                } else {
                                    AtomicOpKind::CompilerFence
                                }
                            );
                            format!("{leaf}:{:?}", atomic.ordering)
                        }
                        Terminator::Opaque { kind, .. }
                            if kind.contains(&format!(
                                "UnsupportedAtomicMetadata({leaf} ordering argument"
                            )) =>
                        {
                            format!("{leaf}:fail-closed")
                        }
                        other => {
                            panic!("{caller}: the real {leaf} lost its atomic reading: {other:?}")
                        }
                    };
                    self.real_fences.push(outcome);
                } else {
                    let Terminator::Call { func: rendered, atomic, .. } = &converted.terminator
                    else {
                        panic!(
                            "{caller}: a user `{leaf}` call must stay a plain Call, got {:?}",
                            converted.terminator
                        )
                    };
                    assert!(callee.is_local(), "{rendered}: fixture callee is the user's");
                    assert!(
                        rendered.ends_with(&format!("::{leaf}")),
                        "{rendered}: the fixture must hit the retired suffix rule"
                    );
                    assert_eq!(identity, AtomicCalleeIdentity::NOT_SYSROOT, "{rendered}");
                    assert!(
                        atomic.is_none(),
                        "{rendered}: a user `{leaf}` is a plain call, not {atomic:?}"
                    );
                    self.user_calls += 1;
                }
            }
        }
        Compilation::Stop
    }
}

#[test]
fn user_fence_named_callees_are_plain_calls_and_real_fences_stay_fences() {
    let mut callbacks = FenceCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "fence_identity".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Copt-level=0".into(),
        "-Zmir-opt-level=1".into(),
        "-Zinline-mir=no".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile fence identity fixture");
    assert_eq!(callbacks.user_calls, 4, "two methods and two free functions observed");
    callbacks.real_fences.sort();
    assert_eq!(
        callbacks.real_fences.iter().map(|o| o.split(':').next().unwrap()).collect::<Vec<_>>(),
        ["compiler_fence", "fence"],
        "control: both real std fences were recognized by identity: {:?}",
        callbacks.real_fences
    );
}
