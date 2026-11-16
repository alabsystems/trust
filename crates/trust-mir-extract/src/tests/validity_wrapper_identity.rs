// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! R107-IDENTITY-1: the extractor stamps std's validity wrappers on `Ty::Adt` from
//! the ADT's DEFINITION (`ty_convert::validity_wrapper_of`): `NonNull` by its
//! `non_null` lang item, `NonZero` by its diagnostic item. The trust-ir bridge's
//! R107 arm charges `src != 0` on a cast into a stamped type, so the charge no
//! longer depends on how the type prints.
//!
//! Two real rustc compilations, each extracted by the production entries on both
//! lanes:
//!
//! * against the sysroot: the transmute into `core::ptr::NonNull` and a
//!   `core::num::NonZero` parameter carry the stamp, and a same-named impostor
//!   `fake::ptr::NonNull` does not (the stamp is the definition's, not the name's;
//!   the bridge's name test is what over-charges an impostor);
//! * `#![no_core]`: the crate's own `#[lang = "non_null"] struct Ptr<T>` IS the
//!   compiler's `NonNull` for that compilation, and the extractor's `ptr_to_nonnull`
//!   leg admits a transmute into it by that lang item. It prints `…::Ptr`, which the
//!   bridge's name test never matched, so before the stamp the admitted cast reached
//!   the bridge with nothing to charge it.

use super::*;

const STD_FIXTURE_PATH: &str = "validity_wrapper_std_fixture.rs";
const STD_FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

pub mod fake {
    pub mod ptr {
        #[repr(transparent)]
        pub struct NonNull<T>(pub *const T);
    }
}

pub fn wrap(p: *const u8) -> core::ptr::NonNull<u8> {
    unsafe { core::mem::transmute::<*const u8, core::ptr::NonNull<u8>>(p) }
}

pub fn nz(n: core::num::NonZero<u32>) -> core::num::NonZero<u32> {
    n
}

pub fn impostor(p: fake::ptr::NonNull<u8>) -> fake::ptr::NonNull<u8> {
    p
}
"#;

const NO_CORE_FIXTURE_PATH: &str = "validity_wrapper_no_core_fixture.rs";
const NO_CORE_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, const_trait_impl, intrinsics, lang_items, no_core, rustc_attrs)]
#![no_core]
#![allow(internal_features)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[lang = "destruct"]
pub const trait Destruct: PointeeSized {}

#[rustc_intrinsic]
pub const unsafe fn transmute<Src, Dst>(src: Src) -> Dst;

#[lang = "non_null"]
#[repr(transparent)]
pub struct Ptr<T> {
    pointer: *const T,
}

#[rustc_diagnostic_item = "NonZero"]
#[repr(transparent)]
pub struct Nz<T>(T);

#[repr(transparent)]
pub struct Plain<T>(T);

pub fn wrap(p: *const u8) -> Ptr<u8> {
    unsafe { transmute::<*const u8, Ptr<u8>>(p) }
}

pub fn nz(n: Nz<u32>) -> Nz<u32> {
    n
}

pub fn plain(n: Plain<u32>) -> Plain<u32> {
    n
}
"#;

struct FixtureFileLoader {
    path: &'static str,
    source: &'static str,
}

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(self.path)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(self.source.into())
        } else {
            Err(io::Error::other("unexpected validity-wrapper fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in this fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

struct Lanes {
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
}

struct WrapperCallbacks {
    path: &'static str,
    source: &'static str,
    functions: BTreeMap<String, Lanes>,
}

impl rustc_driver::Callbacks for WrapperCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader =
            Some(Box::new(FixtureFileLoader { path: self.path, source: self.source }));
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
            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            assert!(self.functions.insert(name, Lanes { logical, faithful }).is_none());
        }
        Compilation::Stop
    }
}

fn extract(path: &'static str, source: &'static str, extra: &[String]) -> BTreeMap<String, Lanes> {
    let mut callbacks = WrapperCallbacks { path, source, functions: BTreeMap::new() };
    let mut args: Vec<String> = vec![
        "rustc".into(),
        path.into(),
        "--crate-name".into(),
        "validity_wrapper_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=3".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
    ];
    args.extend(extra.iter().cloned());
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the validity-wrapper fixture {path}");
    callbacks.functions
}

fn lanes(function: &Lanes) -> [(&'static str, &VerifiableFunction); 2] {
    [("logical", &function.logical), ("faithful", &function.faithful)]
}

/// The `(name, stamp)` of a `Ty::Adt`; panics on any other type.
fn adt_stamp(ty: &Ty) -> (&str, Option<trust_types::ValidityWrapper>) {
    let Ty::Adt { name, validity_wrapper, .. } = ty else {
        panic!("expected a Ty::Adt, got {ty:?}")
    };
    (name.as_str(), *validity_wrapper)
}

/// The target type of every `Rvalue::Cast` in `function`'s body.
fn cast_targets(function: &VerifiableFunction) -> Vec<&Ty> {
    function
        .body
        .blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .filter_map(|stmt| match stmt {
            Statement::Assign { rvalue: Rvalue::Cast(_, target), .. } => Some(target),
            _ => None,
        })
        .collect()
}

/// The one cast into a `Ty::Adt` in `function` (the transmute's target).
fn the_wrapper_cast(
    label: &str,
    function: &VerifiableFunction,
) -> (String, Option<trust_types::ValidityWrapper>) {
    let adts: Vec<_> =
        cast_targets(function).into_iter().filter(|ty| matches!(ty, Ty::Adt { .. })).collect();
    let [target] = adts.as_slice() else {
        panic!("{label}: one cast into an ADT, got {adts:?} in {:#?}", function.body.blocks)
    };
    let (name, stamp) = adt_stamp(target);
    (name.to_string(), stamp)
}

#[test]
fn the_sysroot_wrappers_are_stamped_and_an_impostor_is_not() {
    use trust_types::ValidityWrapper;
    let functions =
        extract(STD_FIXTURE_PATH, STD_FIXTURE_SOURCE, &["--sysroot".into(), compiler_sysroot()]);
    for (lane, function) in lanes(&functions["wrap"]) {
        let (name, stamp) = the_wrapper_cast(lane, function);
        assert!(name.starts_with("core::ptr::non_null::NonNull"), "{lane}: {name}");
        assert_eq!(stamp, Some(ValidityWrapper::NonNull), "{lane}: the transmute's target {name}");
        assert_eq!(
            adt_stamp(&function.body.return_ty).1,
            Some(ValidityWrapper::NonNull),
            "{lane}: the return type"
        );
    }
    for (lane, function) in lanes(&functions["nz"]) {
        let (name, stamp) = adt_stamp(&function.body.return_ty);
        assert!(name.starts_with("core::num::nonzero::NonZero"), "{lane}: {name}");
        assert_eq!(stamp, Some(ValidityWrapper::NonZero), "{lane}: {name}");
    }
    for (lane, function) in lanes(&functions["impostor"]) {
        let (name, stamp) = adt_stamp(&function.body.return_ty);
        assert!(name.contains("fake::ptr::NonNull"), "{lane}: {name}");
        assert_eq!(stamp, None, "{lane}: a same-named impostor is not the lang item: {name}");
    }
}

#[test]
fn a_no_core_crates_own_non_null_lang_item_is_stamped_under_its_own_name() {
    use trust_types::ValidityWrapper;
    let functions =
        extract(NO_CORE_FIXTURE_PATH, NO_CORE_FIXTURE_SOURCE, &["-Ainternal_features".into()]);
    for (lane, function) in lanes(&functions["wrap"]) {
        let (name, stamp) = the_wrapper_cast(lane, function);
        assert!(
            name.ends_with("::Ptr") || name.ends_with("::Ptr<u8>") || name.contains("::Ptr<"),
            "{lane}: the lang item prints under its own name: {name}"
        );
        assert_eq!(
            stamp,
            Some(ValidityWrapper::NonNull),
            "{lane}: `ptr_to_nonnull` admitted this transmute by the lang item, so the \
             charge must reach it whatever it prints: {name}"
        );
    }
    for (lane, function) in lanes(&functions["nz"]) {
        assert_eq!(
            adt_stamp(&function.body.return_ty).1,
            Some(ValidityWrapper::NonZero),
            "{lane}: the `NonZero` diagnostic item"
        );
    }
    for (lane, function) in lanes(&functions["plain"]) {
        assert_eq!(adt_stamp(&function.body.return_ty).1, None, "{lane}: an ordinary newtype");
    }
}
