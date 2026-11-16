// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//! Real MIR controls for the structural forwarding predicate. Local fixture
//! functions never receive P-SPLIT authority: the compiler separately requires
//! authentic core fixed-wrapper and n-ary identities.

use super::*;

const PATH: &str = "debug_wrapper_forwarding.rs";
const SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(fmt_helpers_for_derive)]
use std::fmt::{Debug, Formatter, Result};

pub fn relay_two(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    f.debug_struct_fields_finish(names, &[a, b])
}
pub fn relay_five(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, b: &dyn Debug,
                  c: &dyn Debug, d: &dyn Debug, e: &dyn Debug) -> Result {
    f.debug_struct_fields_finish(names, &[a, b, c, d, e])
}
pub fn relay_copy(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    let copied = names;
    let values = [a, b];
    f.debug_struct_fields_finish(copied, &values)
}
pub fn relay_swapped(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    f.debug_struct_fields_finish(names, &[b, a])
}
pub fn relay_duplicated(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, _b: &dyn Debug) -> Result {
    f.debug_struct_fields_finish(names, &[a, a])
}
pub fn relay_short(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, _b: &dyn Debug) -> Result {
    f.debug_struct_fields_finish(names, &[a])
}
pub fn relay_constant_names(f: &mut Formatter<'_>, _names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    f.debug_struct_fields_finish("Different a b", &[a, b])
}
pub fn relay_reassigned_names(f: &mut Formatter<'_>, mut names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    names = "Different a b";
    f.debug_struct_fields_finish(names, &[a, b])
}
pub fn relay_name_alias(f: &mut Formatter<'_>, mut names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    let alias = &mut names;
    *alias = "Different a b";
    f.debug_struct_fields_finish(names, &[a, b])
}
pub fn relay_reassigned_value<'a>(f: &mut Formatter<'_>, names: &str, mut a: &'a dyn Debug, b: &'a dyn Debug) -> Result {
    a = b;
    f.debug_struct_fields_finish(names, &[a, b])
}
pub fn relay_array_write(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    let mut values = [a, b];
    values[0] = b;
    f.debug_struct_fields_finish(names, &values)
}
#[inline(never)]
fn extra() {}
pub fn relay_extra_call(f: &mut Formatter<'_>, names: &str, a: &dyn Debug, b: &dyn Debug) -> Result {
    extra();
    f.debug_struct_fields_finish(names, &[a, b])
}
pub fn relay_other_receiver(_f: &mut Formatter<'_>, other: &mut Formatter<'_>, names: &str,
                            a: &dyn Debug, b: &dyn Debug) -> Result {
    other.debug_struct_fields_finish(names, &[a, b])
}
"#;

struct Loader;
impl rustc_span::source_map::FileLoader for Loader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(PATH)
    }
    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(SOURCE.into())
        } else {
            Err(io::Error::other("unexpected forwarding fixture path"))
        }
    }
    fn read_binary_file(&self, _: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("no binary fixture inputs"))
    }
    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct Callbacks {
    observed: BTreeMap<String, bool>,
}
impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(Loader));
    }
    fn after_analysis<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            let Some(name) = tcx.opt_item_name(did) else { continue };
            if !name.as_str().starts_with("relay_") {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let calls: Vec<_> = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(bb, data)| {
                    let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                        return None;
                    };
                    let (callee, _) = func.const_fn_def()?;
                    (tcx.item_name(callee).as_str() == "debug_struct_fields_finish").then_some(bb)
                })
                .collect();
            assert_eq!(calls.len(), 1, "fixture keeps its real n-ary call");
            let arity = if name.as_str() == "relay_five" { 5 } else { 2 };
            let accepted = crate::debug_fixed_finisher_forwards_inputs(tcx, body, calls[0], arity);
            assert!(self.observed.insert(name.to_string(), accepted).is_none());
        }
        Compilation::Stop
    }
}

#[test]
fn real_mir_forwarding_preserves_each_original_input_and_refuses_mutation() {
    let mut callbacks = Callbacks::default();
    let args = vec![
        "trustc".into(),
        PATH.into(),
        "--crate-name".into(),
        "debug_forwarding".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
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
    assert!(result.is_ok(), "forwarding fixture compiles");
    let expected = BTreeMap::from([
        ("relay_two".into(), true),
        ("relay_five".into(), true),
        ("relay_copy".into(), true),
        ("relay_swapped".into(), false),
        ("relay_duplicated".into(), false),
        ("relay_short".into(), false),
        ("relay_constant_names".into(), false),
        ("relay_reassigned_names".into(), false),
        ("relay_name_alias".into(), false),
        ("relay_reassigned_value".into(), false),
        ("relay_array_write".into(), false),
        ("relay_extra_call".into(), false),
        ("relay_other_receiver".into(), false),
    ]);
    assert_eq!(callbacks.observed, expected);
}
