// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compiler-owned inline/definition-table enum agreement using actual std Vec
//! and Arc. This fixture reproduces a type-lowering shape, not the production
//! Clean helper or a source-refinement/callee-correctness proof.

use super::*;

const FIXTURE_PATH: &str = "faithful_nested_enum_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

pub enum BigNat { Small(u64), Big(std::vec::Vec<u64>) }
pub enum Literal { Nat(BigNat), String(std::sync::Arc<str>) }
pub struct Cycle { pub lit: Literal, pub next: *const Cycle }
pub fn wrap(lit: Literal, next: *const Cycle) -> Cycle { Cycle { lit, next } }

// A real union has a concrete compiler layout, but its overlapping fields
// are deliberately outside the first-class enum payload policy.
pub union UnsupportedPayload { pub word: u64, pub floating: f64 }
pub enum UnsupportedLiteral { Payload(UnsupportedPayload), Empty }
pub struct UnsupportedCycle {
    pub lit: UnsupportedLiteral,
    pub next: *const UnsupportedCycle,
}
pub fn wrap_unsupported(lit: UnsupportedLiteral, next: *const UnsupportedCycle)
    -> UnsupportedCycle { UnsupportedCycle { lit, next } }
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
            Err(io::Error::other("unexpected nested enum fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in enum fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

struct CompilerEnum {
    name: String,
    variants: Vec<(String, i128, Vec<String>)>,
    layout: trust_types::EnumLayoutInfo,
}

// Read the compiler scalar itself, never the extractor's repr/layout helper.
fn compiler_lane(scalar: rustc_abi::Scalar) -> trust_types::EnumReprHint {
    use rustc_abi::{Integer, Primitive};
    use trust_types::EnumReprHint as R;
    match scalar.primitive() {
        Primitive::Int(Integer::I8, false) => R::U8,
        Primitive::Int(Integer::I8, true) => R::I8,
        Primitive::Int(Integer::I16, false) => R::U16,
        Primitive::Int(Integer::I16, true) => R::I16,
        Primitive::Int(Integer::I32, false) => R::U32,
        Primitive::Int(Integer::I32, true) => R::I32,
        Primitive::Int(Integer::I64, false) => R::U64,
        Primitive::Int(Integer::I64, true) => R::I64,
        other => panic!("fixture enum must have a concrete integer tag/niche, got {other:?}"),
    }
}

fn compiler_enum<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    rust_ty: ty::Ty<'tcx>,
) -> CompilerEnum {
    let ty::TyKind::Adt(definition, _) = rust_ty.kind() else { panic!("actual enum type") };
    assert!(definition.is_enum());
    assert!(definition.repr().int.is_none(), "fixture keeps Rust's actual default repr");
    let layout = tcx
        .layout_of(body.typing_env(tcx).as_query_input(rust_ty))
        .expect("concrete enum has a real compiler layout");
    let rustc_abi::Variants::Multiple { tag, tag_encoding, tag_field, variants: layouts } =
        layout.layout.variants()
    else {
        panic!("both declared fixture variants must have a real tagged layout")
    };
    let offset = layout.layout.fields().offset(tag_field.as_usize()).bytes();
    let lane = compiler_lane(*tag);
    let encoding = match tag_encoding {
        rustc_abi::TagEncoding::Direct => {
            trust_types::EnumTagEncodingInfo::Direct { tag_offset: offset, tag_ty: lane }
        }
        rustc_abi::TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            trust_types::EnumTagEncodingInfo::Niche {
                untagged_variant: untagged_variant.as_u32(),
                niche_variants_start: niche_variants.start.as_u32(),
                niche_variants_end: niche_variants.last.as_u32(),
                niche_start: *niche_start,
                niche_offset: offset,
                niche_ty: lane,
            }
        }
    };
    let mut variants = Vec::new();
    let mut offsets = Vec::new();
    for (index, variant) in definition.variants().iter_enumerated() {
        let discriminant = definition.discriminant_for_variant(tcx, index).val;
        // These fixtures have only implicit nonnegative 0/1 discriminants.
        assert_eq!(discriminant, index.as_usize() as u128);
        variants.push((
            variant.name.to_string(),
            discriminant as i128,
            variant.fields.iter().map(|field| field.name.to_string()).collect(),
        ));
        offsets.push(
            (0..variant.fields.len())
                .map(|field| {
                    layouts[index].field_offsets[rustc_abi::FieldIdx::from_usize(field)].bytes()
                })
                .collect(),
        );
    }
    CompilerEnum {
        name: crate::safe_def_path_str(tcx, definition.did()),
        variants,
        layout: trust_types::EnumLayoutInfo {
            encoding,
            size: layout.size.bytes(),
            align: layout.align.bytes(),
            variant_field_offsets: offsets,
        },
    }
}

struct Modes {
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
    literal: CompilerEnum,
    bignat: Option<CompilerEnum>,
}

#[derive(Default)]
struct EnumCallbacks {
    functions: BTreeMap<String, Modes>,
}

impl rustc_driver::Callbacks for EnumCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        let mut selected = Vec::new();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            if !matches!(name.as_str(), "wrap" | "wrap_unsupported") {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let parameter = body.local_decls[mir::Local::from_usize(1)].ty;
            let literal = compiler_enum(tcx, body, parameter);
            let ty::TyKind::Adt(definition, args) = parameter.kind() else { unreachable!() };
            let nested = definition
                .variants()
                .iter()
                .next()
                .expect("first variant")
                .fields
                .iter()
                .next()
                .expect("first payload")
                .ty(tcx, *args)
                .skip_normalization();
            let ty::TyKind::Adt(nested_def, nested_args) = nested.kind() else {
                panic!("compiler-owned nested payload must be an ADT");
            };
            let bignat = if name == "wrap" {
                let big = nested_def
                    .variants()
                    .iter()
                    .find(|v| v.name.as_str() == "Big")
                    .expect("Big variant")
                    .fields
                    .iter()
                    .next()
                    .expect("Vec payload")
                    .ty(tcx, *nested_args)
                    .skip_normalization();
                let ty::TyKind::Adt(vec_def, _) = big.kind() else { panic!("actual std Vec") };
                assert!(tcx.is_diagnostic_item(rustc_span::sym::Vec, vec_def.did()));
                Some(compiler_enum(tcx, body, nested))
            } else {
                assert!(nested_def.is_union(), "negative uses a real compiler union");
                assert!(tcx.layout_of(body.typing_env(tcx).as_query_input(nested)).is_ok());
                None
            };
            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            let restored = extract_function(tcx, body);
            assert_eq!(logical.content_hash(), restored.content_hash());
            assert_eq!(
                serde_json::to_vec(&logical).expect("logical JSON"),
                serde_json::to_vec(&restored).expect("restored JSON")
            );
            selected.push((name.clone(), did));
            assert!(
                self.functions.insert(name, Modes { logical, faithful, literal, bignat }).is_none()
            );
        }
        assert_eq!(selected.len(), 2, "both distinct real bodies must participate");
        // Reverse the actual HIR-owner visitation order, not a sorted name list.
        // Reuse the same rustc MIR bodies, with each public entry opening its
        // own body-local collector. No authored replacement body is involved.
        for (name, did) in selected.into_iter().rev() {
            let body = tcx.optimized_mir(did);
            let original = &self.functions[&name];
            let faithful = extract_function_faithful(tcx, body);
            assert_same_extraction(&original.faithful, &faithful);
            let logical = extract_function(tcx, body);
            assert_same_extraction(&original.logical, &logical);
        }
        Compilation::Stop
    }
}

fn assert_same_extraction(original: &VerifiableFunction, repeated: &VerifiableFunction) {
    assert_eq!(original.content_hash(), repeated.content_hash(), "body-order hash stability");
    assert_eq!(original.body.datatype_defs, repeated.body.datatype_defs, "body-local definitions");
    assert_eq!(
        serde_json::to_vec(original).expect("initial complete function JSON"),
        serde_json::to_vec(repeated).expect("reverse-order complete function JSON"),
        "body order must not affect any extracted field"
    );
}

fn extract_modes() -> BTreeMap<String, Modes> {
    let mut callbacks = EnumCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "faithful_nested_enum_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=3".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile real std nested enum fixture");
    assert_eq!(
        callbacks.functions.keys().map(String::as_str).collect::<Vec<_>>(),
        ["wrap", "wrap_unsupported"]
    );
    callbacks.functions
}

fn parameter(function: &VerifiableFunction) -> &Ty {
    &function.body.locals.iter().find(|local| local.index == 1).expect("literal parameter").ty
}

fn definition<'a>(function: &'a VerifiableFunction, name: &str) -> &'a Ty {
    trust_types::datatype_definition(&function.body.datatype_defs, name)
        .expect("recursive wrapper must record this exact named definition")
}

fn variant_payload<'a>(ty: &'a Ty, variant: &str) -> &'a Ty {
    let Ty::Adt { variants, .. } = ty else { panic!("complete physical enum required") };
    let fields = &variants.iter().find(|v| v.name == variant).expect("variant").fields;
    assert_eq!(fields.len(), 1);
    &fields[0].1
}

fn assert_compiler_layout(ty: &Ty, expected: &CompilerEnum) {
    let Ty::Adt { name, variants, adt_kind, faithful_enum_repr, enum_layout, .. } = ty else {
        panic!("enum must remain a full physical definition");
    };
    assert_eq!(name, &expected.name);
    assert_eq!(*adt_kind, Some(trust_types::AdtKind::Enum));
    assert_eq!(*faithful_enum_repr, Some(None), "eligible repr(Rust) enum");
    assert_eq!(enum_layout.as_deref(), Some(&expected.layout));
    assert_eq!(
        variants
            .iter()
            .map(|v| (
                v.name.clone(),
                v.discriminant,
                v.fields.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>()
            ))
            .collect::<Vec<_>>(),
        expected.variants
    );
}

#[test]
fn faithful_completed_bignat_definition_keeps_compiler_enum_layout() {
    let modes = extract_modes();
    let modes = &modes["wrap"];
    let expected = modes.bignat.as_ref().expect("compiler BigNat");
    let inline = variant_payload(parameter(&modes.faithful), "Nat");
    let table = definition(&modes.faithful, &expected.name);
    assert_compiler_layout(inline, expected);
    assert_compiler_layout(table, expected);
    assert_eq!(inline, table, "BigNat has no non-sysroot nominal child to abbreviate");
    assert!(matches!(variant_payload(table, "Big"),
        Ty::Adt { adt_kind: Some(trust_types::AdtKind::Struct), layout: Some(_), name, .. }
        if name.ends_with("vec::Vec")));
}

#[test]
fn faithful_nested_literal_definition_matches_inline_compiler_layout() {
    let modes = extract_modes();
    let modes = &modes["wrap"];
    let table = definition(&modes.faithful, &modes.literal.name);
    let nested_marker = variant_payload(table, "Nat");
    assert_eq!(
        trust_types::bare_datatype_marker_name(nested_marker),
        Some(modes.bignat.as_ref().expect("BigNat").name.as_str()),
        "must exercise the actual nominal-child marker, not an inline replacement"
    );
    let completed =
        trust_types::datatype_marker_definition(&modes.faithful.body.datatype_defs, nested_marker)
            .expect("completed exact BigNat definition");
    assert_compiler_layout(completed, modes.bignat.as_ref().expect("BigNat"));
    assert_compiler_layout(parameter(&modes.faithful), &modes.literal);
    assert_compiler_layout(table, &modes.literal);
}

#[test]
fn faithful_union_payload_stays_ineligible_inline_and_in_definition() {
    let modes = extract_modes();
    let modes = &modes["wrap_unsupported"];
    let table = definition(&modes.faithful, &modes.literal.name);
    let marker = variant_payload(table, "Payload");
    assert!(trust_types::bare_datatype_marker_name(marker).is_some());
    let payload =
        trust_types::datatype_marker_definition(&modes.faithful.body.datatype_defs, marker)
            .expect("actual union definition exists");
    assert!(matches!(payload, Ty::Adt { adt_kind: Some(trust_types::AdtKind::Union), .. }));
    for ty in [parameter(&modes.faithful), table] {
        let Ty::Adt { faithful_enum_repr, enum_layout, variants, .. } = ty else {
            panic!("negative still retains its real enum structure");
        };
        assert_eq!(variants.len(), modes.literal.variants.len());
        assert!(
            faithful_enum_repr.is_none(),
            "a completed union must not authorize enum admission"
        );
        assert!(enum_layout.is_none(), "concrete rustc size alone cannot authorize enum layout");
    }
}

#[test]
fn faithful_nested_enum_restores_logical_sequence_payload_and_full_body() {
    let modes = extract_modes();
    let modes = &modes["wrap"];
    let logical_bignat = variant_payload(parameter(&modes.logical), "Nat");
    assert!(matches!(variant_payload(logical_bignat, "Big"), Ty::Seq { .. }));
    let faithful_bignat = variant_payload(parameter(&modes.faithful), "Nat");
    assert!(!matches!(variant_payload(faithful_bignat, "Big"), Ty::Seq { .. }));
    // The callback compared every logical field and the full content hash
    // before/after faithful extraction for BOTH positive and negative bodies.
}

#[test]
fn faithful_nested_enum_reverse_body_order_restores_exact_extractions() {
    // The callback re-extracts both real bodies in reverse HIR-owner order and
    // compares full faithful AND logical payloads, tables and content hashes.
    let modes = extract_modes();
    let accepted = &modes["wrap"];
    let refused = &modes["wrap_unsupported"];
    for faithful in [false, true] {
        let good = if faithful { &accepted.faithful } else { &accepted.logical };
        let bad = if faithful { &refused.faithful } else { &refused.logical };
        assert!(good.body.datatype_defs.contains_key(&accepted.literal.name));
        assert!(bad.body.datatype_defs.contains_key(&refused.literal.name));
        assert!(!good.body.datatype_defs.contains_key(&refused.literal.name));
        assert!(!bad.body.datatype_defs.contains_key(&accepted.literal.name));
    }
}
