// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! FENCE-IDENTITY-1 survey: the derived-comparison sentinels' rendered-path
//! fallback (`safe_def_path_str(trait) == "core::cmp::PartialOrd"`, and the
//! `PartialEq`/`Ord` twins) must not authenticate a trait that merely RENDERS as
//! core's. A crate compiled `--crate-name core` declares its own `cmp` traits
//! with PANICKING impls for `u32`; `tcx_derived_trait_is_total` answers `true`
//! for any primitive `Self`, so before the fix these calls were rewritten to the
//! total sentinel and their panic vanished. The real std comparison on `u32` is
//! the control that still takes the sentinel.

use super::*;

const FIXTURE_PATH: &str = "forged_cmp_identity_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]
pub mod cmp {
    pub trait PartialEq { fn eq(&self, other: &Self) -> bool; }
    pub trait PartialOrd { fn lt(&self, other: &Self) -> bool; }
    pub trait Ord { fn cmp(&self, other: &Self) -> u8; }
    impl PartialEq for u32 { fn eq(&self, _: &Self) -> bool { panic!("forged eq") } }
    impl PartialOrd for u32 { fn lt(&self, _: &Self) -> bool { panic!("forged lt") } }
    impl Ord for u32 { fn cmp(&self, _: &Self) -> u8 { panic!("forged cmp") } }
}
pub fn forged_eq(a: u32, b: u32) -> bool { cmp::PartialEq::eq(&a, &b) }
pub fn forged_lt(a: u32, b: u32) -> bool { cmp::PartialOrd::lt(&a, &b) }
pub fn forged_cmp(a: u32, b: u32) -> u8 { cmp::Ord::cmp(&a, &b) }
pub fn real_eq(a: u32, b: u32) -> bool { std::cmp::PartialEq::eq(&a, &b) }
pub fn real_lt(a: u32, b: u32) -> bool { std::cmp::PartialOrd::lt(&a, &b) }
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
            Err(io::Error::other("unexpected forged-cmp fixture source path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported in forged-cmp fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct ForgedCmpCallbacks {
    forged: Vec<String>,
    real: Vec<String>,
}

impl rustc_driver::Callbacks for ForgedCmpCallbacks {
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
            let forged = match caller.as_str() {
                "forged_eq" | "forged_lt" | "forged_cmp" => true,
                "real_eq" | "real_lt" => false,
                _ => continue,
            };
            let body = tcx.optimized_mir(did);
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    continue;
                };
                let Some((callee, _)) = func.const_fn_def() else { continue };
                let Some(trait_did) = tcx.trait_of_assoc(callee) else { continue };
                let trait_path = crate::safe_def_path_str(tcx, trait_did);
                let converted = crate::convert::convert_basic_block(
                    tcx,
                    bb,
                    data,
                    Some(body),
                    Some(body.typing_env(tcx)),
                    Some(body.source.def_id()),
                    crate::convert::OptionalOverflowAssertCodegen::ThisSession,
                );
                let Terminator::Call { func: rendered, .. } = &converted.terminator else {
                    panic!("{caller}: a comparison call stays a Call: {:?}", converted.terminator)
                };
                if forged {
                    assert!(trait_did.is_local(), "{caller}: the fixture trait is the local one");
                    assert!(
                        matches!(
                            trait_path.as_str(),
                            "core::cmp::PartialEq" | "core::cmp::PartialOrd" | "core::cmp::Ord"
                        ),
                        "{caller}: the fixture must render as core's trait to hit the \
                         fallback, rendered {trait_path}"
                    );
                    assert!(!crate::convert::is_real_sysroot_crate(tcx, trait_did.krate));
                    assert_ne!(
                        rendered,
                        trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL,
                        "{caller}: a forged `{trait_path}` impl that panics must keep its call"
                    );
                    self.forged.push(caller.clone());
                } else {
                    assert_eq!(
                        rendered,
                        trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL,
                        "{caller}: control — the real `{trait_path}` on u32 is total"
                    );
                    self.real.push(caller.clone());
                }
            }
        }
        Compilation::Stop
    }
}

#[test]
fn forged_core_cmp_traits_never_take_the_total_sentinel() {
    let mut callbacks = ForgedCmpCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        // The impersonation under test: the local crate's own `cmp` traits render
        // as `core::cmp::*` through the unstamped `safe_def_path_str`.
        "core".into(),
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
    assert!(result.is_ok(), "failed to compile forged-cmp fixture");
    callbacks.forged.sort();
    callbacks.real.sort();
    assert_eq!(callbacks.forged, ["forged_cmp", "forged_eq", "forged_lt"]);
    assert_eq!(callbacks.real, ["real_eq", "real_lt"]);
}
