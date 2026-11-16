// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! REPR-U128-HIGH-TAG-1: an enum one of whose tags has no `i128` denotation (a
//! `#[repr(u128)]` tag above `i128::MAX`) must not reach the dump as a modeled
//! `Ty::Adt`. `VariantDef::discriminant` is an `i128`; the extractor used to store
//! such a tag as the lossy `val as i128` (`u128::MAX` as `-1`, `1 << 127` as
//! `i128::MIN`), and `trust_vcgen`'s discriminant-domain fact then said
//! `d ∈ {0, -1, 5}` about a `u128` read whose switch label is the true
//! `u128::MAX`: the arm for that variant was UNSAT and every row in it was proved
//! (measured on the stage 1 of main `2bf0ad72e3`; `tests/ui/trust/
//! repr_u128_high_tag_no_false_proof.rs`).
//!
//! These are real rustc bodies, extracted by the production entries on both lanes.
//! The controls pin the boundary: a `#[repr(u128)]` tag AT `i128::MAX` and a
//! `#[repr(i128)]` tag at `i128::MIN` have an `i128` denotation and stay modeled
//! with their true tags.

use super::*;

const FIXTURE_PATH: &str = "repr_u128_high_tag_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

#[repr(u128)]
#[derive(Clone, Copy)]
pub enum Max { A = 0, B = u128::MAX, C = 5 }

#[repr(u128)]
#[derive(Clone, Copy)]
pub enum Top { A = 0, B = 1u128 << 127, C = 3 }

#[repr(u128)]
pub enum Payload { A(u8) = 0, B(u8) = u128::MAX, C = 3 }

#[repr(u128)]
pub enum List { Nil = 0, Cons(Box<List>) = u128::MAX }

#[repr(u128)]
#[derive(Clone, Copy)]
pub enum Fits { A = 0, B = i128::MAX as u128, C = 5 }

#[repr(i128)]
#[derive(Clone, Copy)]
pub enum Signed { A = 0, B = i128::MIN, C = 5 }

pub fn max(e: Max, x: u8) -> u8 { if let Max::B = e { x + 1 } else { 0 } }
pub fn top(e: Top, x: u8) -> u8 { if let Top::B = e { x + 1 } else { 0 } }
pub fn payload(e: &Payload) -> u8 { match e { Payload::B(x) => *x + 1, _ => 0 } }
pub fn list(l: &List) -> u8 { match l { List::Cons(_) => 1, List::Nil => 0 } }
pub fn fits(e: Fits, x: u8) -> u8 { if let Fits::B = e { x + 1 } else { 0 } }
pub fn signed(e: Signed, x: u8) -> u8 { if let Signed::B = e { x + 1 } else { 0 } }
"#;

const FUNCTIONS: [&str; 6] = ["fits", "list", "max", "payload", "signed", "top"];

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected repr(u128) fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in the repr(u128) fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

struct Lanes {
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
}

#[derive(Default)]
struct HighTagCallbacks {
    functions: BTreeMap<String, Lanes>,
}

impl rustc_driver::Callbacks for HighTagCallbacks {
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
            let name = tcx.item_name(did).to_string();
            if !FUNCTIONS.contains(&name.as_str()) {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            assert!(self.functions.insert(name, Lanes { logical, faithful }).is_none());
        }
        Compilation::Stop
    }
}

fn extract_fixture() -> BTreeMap<String, Lanes> {
    let mut callbacks = HighTagCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "repr_u128_high_tag_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the repr(u128) high-tag fixture");
    assert_eq!(callbacks.functions.keys().map(String::as_str).collect::<Vec<_>>(), FUNCTIONS);
    callbacks.functions
}

fn lanes(function: &Lanes) -> [(&'static str, &VerifiableFunction); 2] {
    [("logical", &function.logical), ("faithful", &function.faithful)]
}

/// The declared type of local 1 — the enum parameter, or the pointee of `&Enum`.
fn scrutinee(function: &VerifiableFunction) -> &Ty {
    let declared =
        &function.body.locals.iter().find(|local| local.index == 1).expect("parameter 1").ty;
    match declared {
        Ty::Ref { inner, .. } => &**inner,
        other => other,
    }
}

/// Every `VariantDef::discriminant` the dump carries anywhere — locals, return
/// type, nested payloads and the datatype table — read off the serialized JSON
/// TEXT, so no corner of the `Ty` tree is skipped. (Text, not `serde_json::Value`:
/// the body's `u128::MAX` switch label does not fit a `Value` number.)
fn every_discriminant(function: &VerifiableFunction) -> Vec<i128> {
    const KEY: &str = "\"discriminant\":";
    let text = serde_json::to_string(function).expect("extracted function serializes");
    text.match_indices(KEY)
        .map(|(at, _)| {
            let rest = &text[at + KEY.len()..];
            let end = rest
                .char_indices()
                .find(|&(i, c)| !(c.is_ascii_digit() || (i == 0 && c == '-')))
                .map_or(rest.len(), |(i, _)| i);
            rest[..end]
                .parse()
                .unwrap_or_else(|_| panic!("discriminant `{}` must be an integer", &rest[..end]))
        })
        .collect()
}

/// THE FIX. A tag above `i128::MAX` makes the whole enum the fail-closed
/// `Unsupported` leaf, on both lanes, and no false tag reaches the dump.
#[test]
fn repr_u128_tag_above_i128_max_lowers_to_unsupported() {
    let functions = extract_fixture();
    for name in ["max", "top", "payload"] {
        for (lane, function) in lanes(&functions[name]) {
            let Ty::Unsupported { kind, detail } = scrutinee(function) else {
                panic!(
                    "{name} ({lane}): an enum with a tag above i128::MAX must not be a modeled \
                     type, got {:?}",
                    scrutinee(function)
                );
            };
            assert_eq!(kind, "TyKind::Adt", "{name} ({lane})");
            assert!(detail.contains("REPR-U128-HIGH-TAG-1"), "{name} ({lane}): {detail}");
            // The prefix is load-bearing in trust-vcgen: a `recursive` detail skips
            // the declaration marker. This enum is not recursive, so its locals must
            // keep stamping their `UnsupportedMir` row.
            assert!(!detail.starts_with("recursive"), "{name} ({lane}): {detail}");
            assert_eq!(
                every_discriminant(function),
                Vec::<i128>::new(),
                "{name} ({lane}): no variant table may survive for this enum"
            );
        }
    }
}

/// A RECURSIVE enum with such a tag is a cut point: its use site is the by-name
/// marker, and its definition is the `Unsupported` leaf, which the table refuses
/// (it has no name) — a marker with no definition, which every consumer declines.
#[test]
fn recursive_repr_u128_high_tag_enum_records_no_definition() {
    let functions = extract_fixture();
    for (lane, function) in lanes(&functions["list"]) {
        assert_eq!(
            every_discriminant(function),
            Vec::<i128>::new(),
            "list ({lane}): the lossy `-1` must not reach the datatype table"
        );
        assert!(
            !function.body.datatype_defs.keys().any(|name| name.contains("List")),
            "list ({lane}): no definition may be recorded for the enum: {:?}",
            function.body.datatype_defs.keys().collect::<Vec<_>>()
        );
    }
}

/// CONTROLS: a tag that HAS an `i128` denotation keeps the modeled enum and its
/// true tag — `i128::MAX` under `repr(u128)`, and the genuinely negative
/// `i128::MIN` under `repr(i128)`.
#[test]
fn tags_with_an_i128_denotation_stay_modeled() {
    let functions = extract_fixture();
    for (name, expected) in [("fits", [0, i128::MAX, 5]), ("signed", [0, i128::MIN, 5])] {
        for (lane, function) in lanes(&functions[name]) {
            let Ty::Adt { variants, .. } = scrutinee(function) else {
                panic!("{name} ({lane}): must stay a modeled enum, got {:?}", scrutinee(function));
            };
            assert_eq!(
                variants.iter().map(|variant| variant.discriminant).collect::<Vec<_>>(),
                expected,
                "{name} ({lane})"
            );
        }
    }
}
