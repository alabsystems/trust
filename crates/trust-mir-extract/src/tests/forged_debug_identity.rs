// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! An external crate can render as std::fmt::Formatter without being core's
//! Formatter. Its real call and metadata must survive both extraction modes.

use super::*;

const FOREIGN_SOURCE: &str = r#"
#![no_std]
pub mod fmt {
    pub struct Formatter;
    impl Formatter {
        #[inline(never)]
        pub fn debug_struct_field2_finish(
            &mut self, _: &str, _: &dyn core::fmt::Debug, _: &dyn core::fmt::Debug,
        ) -> core::fmt::Result { panic!("foreign fixed helper") }
        #[inline(never)]
        pub fn debug_struct_fields_finish(
            &mut self, _: &str, _: &[&dyn core::fmt::Debug],
        ) -> core::fmt::Result { panic!("foreign nary helper") }
    }
}
"#;

const CALLER_SOURCE: &str = r#"
#![no_std]
extern crate foreign_std;
pub fn forged_fixed() -> core::fmt::Result {
    let mut f = foreign_std::fmt::Formatter;
    f.debug_struct_field2_finish("Good first second", &1u64, &2u64)
}
pub fn forged_nary() -> core::fmt::Result {
    let mut f = foreign_std::fmt::Formatter;
    f.debug_struct_fields_finish("Good first second", &[&1u64, &2u64])
}
"#;

struct OwnedFixtureDir(std::path::PathBuf);

impl OwnedFixtureDir {
    fn create() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let base = std::env::current_dir().expect("test working directory").join("target");
        std::fs::create_dir_all(&base).expect("fixture output parent");
        for _ in 0..100 {
            let path = base.join(format!(
                "forged-debug-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture directory: {error}"),
            }
        }
        panic!("no unused fixture directory");
    }
}

impl Drop for OwnedFixtureDir {
    fn drop(&mut self) {
        // The directory was created exclusively by this test.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct DependencyCallbacks;
impl rustc_driver::Callbacks for DependencyCallbacks {}

fn call_at(function: &VerifiableFunction, block: BlockId) -> &Terminator {
    &function.body.blocks.iter().find(|entry| entry.id == block).expect("same MIR block").terminator
}

#[derive(Default)]
struct CallerCallbacks {
    seen: Vec<String>,
}

impl rustc_driver::Callbacks for CallerCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            if !matches!(name.as_str(), "forged_fixed" | "forged_nary") {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            let restored = extract_function(tcx, body);
            assert_eq!(logical.content_hash(), restored.content_hash());
            let mut calls = 0;
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    continue;
                };
                let Some((callee, generic_args)) = func.const_fn_def() else { continue };
                if !matches!(
                    tcx.item_name(callee).as_str(),
                    "debug_struct_field2_finish" | "debug_struct_fields_finish"
                ) {
                    continue;
                }
                calls += 1;
                assert!(!callee.is_local(), "must test the external-DefId path");
                assert!(!crate::is_real_sysroot_crate(tcx, callee.krate));
                let rendered = crate::safe_def_path_str(tcx, callee);
                assert!(rendered.starts_with("std::fmt::Formatter"), "{rendered}");
                let identity = crate::convert::callee_identity_for(tcx, callee, generic_args)
                    .expect("concrete foreign helper identity");
                let key = crate::convert::callee_key_for(tcx, callee);
                let Terminator::Call { func, callee_identity, callee_key, .. } =
                    call_at(&logical, BlockId(bb.as_usize()))
                else {
                    panic!("foreign call must remain a call");
                };
                assert_ne!(func, crate::convert::TRUST_TOTAL_CLONE_SENTINEL);
                assert_eq!(*callee_identity, Some(identity));
                assert_eq!(callee_key.as_ref(), Some(&key));
                assert_eq!(
                    serde_json::to_value(call_at(&logical, BlockId(bb.as_usize())))
                        .expect("logical call"),
                    serde_json::to_value(call_at(&faithful, BlockId(bb.as_usize())))
                        .expect("faithful call")
                );
            }
            assert_eq!(calls, 1, "{name} must exercise one external helper");
            self.seen.push(name);
        }
        Compilation::Stop
    }
}

fn compile(args: &[String], callbacks: &mut (dyn rustc_driver::Callbacks + Send)) {
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(args, callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "foreign Debug fixture compilation failed");
}

#[test]
fn external_std_formatter_lookalikes_keep_both_real_calls() {
    let directory = OwnedFixtureDir::create();
    let foreign = directory.0.join("foreign.rs");
    let caller = directory.0.join("caller.rs");
    let metadata = directory.0.join("libstd.rmeta");
    std::fs::write(&foreign, FOREIGN_SOURCE).expect("foreign fixture source");
    std::fs::write(&caller, CALLER_SOURCE).expect("caller fixture source");
    let sysroot = compiler_sysroot();
    let mut dependency_callbacks = DependencyCallbacks;
    compile(
        &[
            "rustc".into(),
            foreign.display().to_string(),
            "--crate-name=std".into(),
            "--crate-type=rlib".into(),
            "--edition=2021".into(),
            "--emit=metadata".into(),
            "-Zcodegen-backend=dummy".into(),
            "--sysroot".into(),
            sysroot.clone(),
            "-o".into(),
            metadata.display().to_string(),
        ],
        &mut dependency_callbacks,
    );
    assert!(metadata.is_file(), "must load an actual external metadata artifact");
    let mut callbacks = CallerCallbacks::default();
    compile(
        &[
            "rustc".into(),
            caller.display().to_string(),
            "--crate-name=debug_caller".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Zmir-opt-level=0".into(),
            "-Zinline-mir=no".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            "--sysroot".into(),
            sysroot,
            "--extern".into(),
            format!("foreign_std={}", metadata.display()),
        ],
        &mut callbacks,
    );
    callbacks.seen.sort();
    assert_eq!(callbacks.seen, ["forged_fixed", "forged_nary"]);
}
