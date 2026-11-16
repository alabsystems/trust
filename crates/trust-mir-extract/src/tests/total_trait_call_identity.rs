// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Rendered Default/PartialEq paths do not establish associated methods.
use super::*;

const FIXTURE_PATH: &str = "total_trait_call_identity_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code, non_snake_case)]
mod Default {
    #[inline(never)] pub fn default() -> Option<u32> { panic!("free default") }
}
mod generic {
    pub mod Default {
        #[inline(never)] pub fn default<T>() -> Option<T> { panic!("generic free default") }
    }
}
mod local {
    pub trait Default { fn default() -> Option<u32>; }
    pub struct Value;
    impl Default for Value {
        #[inline(never)] fn default() -> Option<u32> { panic!("local trait default") }
    }
}
pub fn free_default() -> Option<u32> { Default::default() }
pub fn generic_free_default() -> Option<u32> { generic::Default::default::<u32>() }
pub fn local_trait_default() -> Option<u32> { <local::Value as local::Default>::default() }
pub fn real_option_default() -> Option<u32> { core::default::Default::default() }
mod PartialEq {
    #[inline(never)] pub fn eq<T>() -> bool { panic!("generic free eq") }
    #[inline(never)] pub fn ne<T>() -> bool { panic!("generic free ne") }
}
mod non_generic {
    pub mod PartialEq {
        #[inline(never)] pub fn eq() -> bool { panic!("free eq") }
        #[inline(never)] pub fn ne() -> bool { panic!("free ne") }
    }
}
pub fn generic_free_eq() -> bool { PartialEq::eq::<u32>() }
pub fn generic_free_ne() -> bool { PartialEq::ne::<u32>() }
pub fn nongeneric_free_eq() -> bool { non_generic::PartialEq::eq() }
pub fn nongeneric_free_ne() -> bool { non_generic::PartialEq::ne() }
pub fn real_eq(a: u32, b: u32) -> bool { core::cmp::PartialEq::eq(&a, &b) }
pub fn real_ne(a: u32, b: u32) -> bool { core::cmp::PartialEq::ne(&a, &b) }

"#;

const CALLERS: &[&str] = &[
    "free_default",
    "generic_free_default",
    "local_trait_default",
    "real_option_default",
    "generic_free_eq",
    "generic_free_ne",
    "nongeneric_free_eq",
    "nongeneric_free_ne",
    "real_eq",
    "real_ne",
];

struct FixtureFileLoader;
impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }
    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected total-trait-identity fixture path"))
        }
    }
    fn read_binary_file(&self, _: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported in total-trait-identity fixture"))
    }
    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct TraitIdentityCallbacks {
    observed: BTreeSet<String>,
}
impl rustc_driver::Callbacks for TraitIdentityCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }
    fn after_analysis<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            let caller = tcx.item_name(did).to_string();
            if !CALLERS.contains(&caller.as_str()) {
                continue;
            }
            let body = tcx.optimized_mir(did);
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    continue;
                };
                let Some((callee, args)) = func.const_fn_def() else {
                    continue;
                };
                let rendered_before = crate::safe_def_path_str(tcx, callee);
                let converted = crate::convert::convert_basic_block(
                    tcx,
                    bb,
                    data,
                    Some(body),
                    Some(body.typing_env(tcx)),
                    Some(body.source.def_id()),
                    crate::convert::OptionalOverflowAssertCodegen::ThisSession,
                );
                let Terminator::Call { func: rendered_after, .. } = converted.terminator else {
                    panic!("{caller}: the source call must stay a Call")
                };
                if matches!(caller.as_str(), "real_option_default" | "real_eq" | "real_ne") {
                    assert_eq!(
                        rendered_after,
                        trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL,
                        "{caller}: the authentic core trait implementation remains total"
                    );
                } else {
                    assert!(
                        rendered_before.ends_with("::default")
                            || rendered_before.ends_with("::eq")
                            || rendered_before.ends_with("::ne"),
                        "must exercise a total-trait matcher spelling: {rendered_before}"
                    );
                    assert_ne!(
                        rendered_after,
                        trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL,
                        "{caller}: a free function or local trait that panics keeps its real call"
                    );
                    if caller != "local_trait_default" {
                        assert_eq!(tcx.def_kind(callee), rustc_hir::def::DefKind::Fn);
                        if matches!(caller.as_str(), "generic_free_eq" | "generic_free_ne") {
                            assert!(
                                args.types().next().is_some(),
                                "generic free calls must pass the old type-argument gate"
                            );
                        }
                    }
                }
                assert!(self.observed.insert(caller.clone()), "one source call per witness");
            }
        }
        Compilation::Stop
    }
}

#[test]
fn trait_path_spelling_never_turns_free_functions_into_associated_items() {
    let mut callbacks = TraitIdentityCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "total_trait_call_identity".into(),
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
    assert!(result.is_ok(), "failed to compile total-trait identity fixture");
    assert_eq!(callbacks.observed, CALLERS.iter().map(|name| (*name).to_owned()).collect());
}
