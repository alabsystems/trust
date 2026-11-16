// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Trust (2026-11-07): `ctfe_reentrancy::walk_types_until` visits each DISTINCT type
//! once, as `TypeWalker`'s visited table does. 3607f0f8997 dropped the table, which
//! made the walk exponential in the depth of a type whose subterms are shared
//! (`PolyBox<(T, T)>`: more than 45 CPU minutes in
//! `tests/ui/trust/assume_total_does_not_cover_callee_requires.rs`). A regression
//! there hangs compiletest instead of failing it; this test fails fast instead: the
//! visitor stops after a budget far above the distinct count, so a walk that repeats
//! shared subterms returns `false` and over-counts.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::*;

const PATH: &str = "walk_types_shared_subterms.rs";

/// `D0 = (u8, u8)`, `Dk = (D{k-1}, D{k-1})` up to `D20`: 22 distinct types (`u8` and
/// `D0..=D20`), but 2^22 nodes in the tree a walk without a visited table expands.
/// Kept at 20: rustc's own late-bound-region collector over the signature expands
/// the tree too, and depth 40 does not finish.
fn source() -> String {
    let mut source = String::from("#![allow(dead_code)]\ntype D0 = (u8, u8);\n");
    for depth in 1..=20 {
        source.push_str(&format!("type D{depth} = (D{prev}, D{prev});\n", prev = depth - 1));
    }
    source.push_str("fn deep(_: D20) {}\n");
    source
}

struct Loader;

impl rustc_span::source_map::FileLoader for Loader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(source())
        } else {
            Err(io::Error::other("unexpected walk fixture path"))
        }
    }

    fn read_binary_file(&self, _: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("fixture does not read binary source"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

/// Far above the 22 distinct types, far below the 2^22 repeated visits.
const BUDGET: usize = 10_000;

#[derive(Default)]
struct Probe {
    observed: Option<(bool, usize)>,
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
            if tcx.item_name(did).as_str() != "deep" {
                continue;
            }
            let signature = tcx.fn_sig(did).instantiate_identity().skip_norm_wip().skip_binder();
            let input = signature.inputs()[0];
            let mut visits = 0usize;
            let completed = crate::ctfe_reentrancy::walk_types_until(input, |_| {
                visits += 1;
                visits <= BUDGET
            });
            assert!(self.observed.replace((completed, visits)).is_none());
        }
        rustc_driver::Compilation::Stop
    }
}

#[test]
fn walk_types_until_visits_each_shared_subterm_once() {
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
    assert!(result.is_ok(), "the walk fixture must compile");
    // `u8` and `D0..=D20`, each once.
    assert_eq!(probe.observed, Some((true, 22)), "each distinct type is visited once");
}
