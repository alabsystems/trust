//! BMC-LANE-1 hostile review 4, F1: the native lane's R107 charge (a `p != 0`
//! assert before a cast into `NonNull`/`NonZero`) skips only a bundled member the
//! compiler authenticated as a foreign `core`/`alloc`/`std` body. It used to skip
//! any body whose printed def path was rooted at `core::`/`alloc::`/`std::`. A
//! bundle ROOT's def path is printed without the impersonation stamp, so a user
//! crate built `--crate-name core` (an ordinary invocation, no
//! `-Zforce-unstable-if-unmarked`) printed its own `wrap` as `core::wrap` and lost
//! the charge: 0 asserts where `--crate-name mycrate` had 1 (measured 2026-11-09).
//!
//! Hostile review 5, F1: the genuine `core`, loaded from outside this compiler's
//! sysroot, lost the charge too. The extractor prints every type of a non-resident
//! `core` under the unauthenticated-crate stamp (`__trust_crate@<id>::core::ptr::
//! non_null::NonNull`), and the arm's bare prefix test missed that name: a
//! `#![no_std]` `wrap` built with `--extern core=<a copy of the sysroot's libcore>`
//! had 0 asserts where the resident `core` gave 1 (measured 2026-11-09). That is the
//! `cargo -Zbuild-std` lane.
//!
//! R107-IDENTITY-1: a genuine wrapper under a name no spelling lists lost the charge
//! too. A `#![no_core]` crate's own `#[lang = "non_null"]` struct IS that
//! compilation's `NonNull` (the extractor's `ptr_to_nonnull` admits a transmute into
//! it by the lang item), and it prints `mycrate::Ptr`, which the name test never
//! matched. The extractor now stamps the type's identity from its definition
//! (`Ty::Adt::validity_wrapper`), and the charge follows the stamp.
//!
//! Every build fails, on the MIR `[unsafe:validity-transmute]` row, which keys on the
//! crate's identity. What this pins is the native bundle itself: the same source must
//! carry the same charge under either name and against either `core`, and a crate's
//! own `non_null` lang item must carry it under its own name.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

/// Set by compiletest's `--trust-vanilla` replay, which runs the stock rustc.
/// That build has no verifier and writes no bundle, so there is nothing to assert.
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

const SOURCE: &str = "use std::ptr::NonNull;\n\
                      pub fn wrap(p: *const u8) -> NonNull<u8> {\n\
                      \x20   unsafe { std::mem::transmute::<*const u8, NonNull<u8>>(p) }\n\
                      }\n";

/// The same `wrap` against `core` alone, for the build that supplies `core` itself.
const NO_STD_SOURCE: &str = "#![no_std]\n\
                             use core::ptr::NonNull;\n\
                             pub fn wrap(p: *const u8) -> NonNull<u8> {\n\
                             \x20   unsafe { core::mem::transmute::<*const u8, NonNull<u8>>(p) }\n\
                             }\n";

/// The same `wrap` into a `#![no_core]` crate's own `non_null` lang item, declared as
/// `core` declares `NonNull` (a `*const T is !null` pattern-type field, so a null
/// pointer is invalid for it and the transmute owes the charge).
const NO_CORE_SOURCE: &str = r#"#![feature(auto_traits, const_trait_impl, intrinsics, lang_items, no_core, pattern_types, rustc_attrs)]
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

#[rustc_builtin_macro(pattern_type)]
macro_rules! pattern_type {
    ($($arg:tt)*) => {
        /* compiler built-in */
    };
}

#[rustc_intrinsic]
pub const unsafe fn transmute<Src, Dst>(src: Src) -> Dst;

#[lang = "non_null"]
#[repr(transparent)]
pub struct Ptr<T> {
    pointer: pattern_type!(*const T is !null),
}

pub fn wrap(p: *const u8) -> Ptr<u8> {
    unsafe { transmute::<*const u8, Ptr<u8>>(p) }
}
"#;

/// The `(ICmp, Assert)` counts in `wrap`'s body of the one bundle a build of
/// `source` named `crate_name` writes; `label` names the build's own directories.
fn r107_charge(
    trustc: &PathBuf,
    label: &str,
    crate_name: &str,
    source: &str,
    extra: &[String],
) -> (usize, usize) {
    let dump = format!("native-bundle-{label}");
    cmd(trustc)
        .args([
            "--edition=2021",
            "--crate-type=lib",
            "--emit=metadata",
            &format!("--crate-name={crate_name}"),
            &format!("--out-dir=out-{label}"),
            "-Ztrust-verify=on",
            &format!("-Ztrust-dump=native-bundle:{dump}"),
        ])
        .args(extra)
        .arg(source)
        // `run_unchecked`: the MIR row refuses the unproved transmute in every
        // build, so each exits nonzero; the bundle is what is measured.
        .run_unchecked();

    let bundles: Vec<PathBuf> = rfs::read_dir(&dump)
        .filter_map(|entry| {
            let path = entry.expect("read native-bundle directory entry").path();
            let name = path.file_name()?.to_string_lossy().into_owned();
            (name.starts_with("trust-native-bundle-") && name.ends_with(".json")).then_some(path)
        })
        .collect();
    let [bundle] = bundles.as_slice() else {
        panic!("{label}: expected one native bundle, got {bundles:?}")
    };
    let json: serde_json::Value =
        serde_json::from_slice(&rfs::read(bundle)).expect("the bundle must be valid JSON");
    let functions =
        json["module"]["functions"].as_array().expect("the bundle module must carry functions");
    let [wrap] = functions.as_slice() else {
        panic!("{label}: expected `wrap` alone, got {} functions", functions.len())
    };
    let mut counts = (0, 0);
    for block in wrap["blocks"].as_array().expect("a function has blocks") {
        for node in block["body"].as_array().expect("a block has a body") {
            let inst = &node["inst"];
            if inst.get("ICmp").is_some() {
                counts.0 += 1;
            }
            if inst.get("Assert").is_some() {
                counts.1 += 1;
            }
        }
    }
    counts
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }
    rfs::write("wrap.rs", SOURCE);
    rfs::write("wrap_no_std.rs", NO_STD_SOURCE);
    rfs::write("wrap_no_core.rs", NO_CORE_SOURCE);

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    let control = r107_charge(&trustc, "mycrate", "mycrate", "wrap.rs", &[]);
    assert_eq!(control, (1, 1), "the control must carry R107's one `p != 0` compare and assert");
    let impersonator = r107_charge(&trustc, "core", "core", "wrap.rs", &[]);
    assert_eq!(
        impersonator, control,
        "a user crate named `core` must be charged like any other: its root prints \
         `core::wrap`, and only the compiler's own authentication may exempt a body"
    );

    // The genuine `core`, from the sysroot and from a copy outside it.
    let resident = r107_charge(&trustc, "no-std-resident", "mycrate", "wrap_no_std.rs", &[]);
    assert_eq!(resident, (1, 1), "a `#![no_std]` cast into the resident `core`'s NonNull");
    let libdir = PathBuf::from(
        cmd(&trustc).arg("--print=target-libdir").run().stdout_utf8().trim().to_string(),
    );
    let libcore = |extension: &str| {
        rfs::read_dir(&libdir)
            .map(|entry| entry.expect("read the target library directory").path())
            .find(|path| {
                path.file_name().is_some_and(|name| {
                    let name = name.to_string_lossy();
                    name.starts_with("libcore-") && name.ends_with(extension)
                })
            })
    };
    let libcore = libcore(".rmeta")
        .or_else(|| libcore(".rlib"))
        .unwrap_or_else(|| panic!("no libcore in {}", libdir.display()));
    rfs::create_dir_all("extern-core");
    let copy = PathBuf::from("extern-core").join(libcore.file_name().expect("a file name"));
    rfs::copy(&libcore, &copy);
    let copy = std::fs::canonicalize(&copy).expect("canonicalize the copied libcore");
    let extern_core = r107_charge(
        &trustc,
        "no-std-extern-core",
        "mycrate",
        "wrap_no_std.rs",
        &["--extern".to_string(), format!("core={}", copy.display())],
    );
    assert_eq!(
        extern_core, resident,
        "the genuine `core` loaded from outside the sysroot (its types print stamped \
         `__trust_crate@<id>::core::…`) must be charged like the resident one"
    );

    // A crate's own `non_null` lang item, under its own name.
    let no_core = r107_charge(&trustc, "no-core-lang-item", "mycrate", "wrap_no_core.rs", &[]);
    assert_eq!(
        no_core, control,
        "a `#![no_core]` crate's own `non_null` lang item prints `mycrate::Ptr`; the \
         extractor's identity stamp, not the name, must carry the charge"
    );
}
