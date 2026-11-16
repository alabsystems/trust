// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compiler-owned real-Vec mode separation, not a hand-authored MIR fixture.
//!
//! These tests need the matching Trust core/alloc/std metadata. They exercise
//! extraction only, with no code generation, proof verdict or Clean-helper claim.

use super::*;

const FIXTURE_PATH: &str = "faithful_real_vec_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

pub struct Node {
    pub children: std::vec::Vec<Node>,
}

pub mod fake {
    pub struct Vec<T> {
        pub payload: T,
        pub stamp: u8,
    }
}

pub fn vector_u64(value: std::vec::Vec<u64>) -> std::vec::Vec<u64> { value }
pub fn vector_u8(value: std::vec::Vec<u8>) -> std::vec::Vec<u8> { value }
pub fn recursive_node(value: Node) -> Node { value }
pub fn recursive_vector(value: std::vec::Vec<Node>) -> std::vec::Vec<Node> { value }
pub fn fake_vector(value: fake::Vec<u64>) -> fake::Vec<u64> { value }
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
            Err(io::Error::other("unexpected faithful Vec fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in Vec fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

struct CompilerShape {
    fields: Vec<String>,
    offsets: Vec<u64>,
    size: u64,
    align: u64,
}

struct Modes {
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
    shape: CompilerShape,
}

#[derive(Default)]
struct VecCallbacks {
    functions: BTreeMap<String, Modes>,
}

impl rustc_driver::Callbacks for VecCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for def_id in tcx.hir_body_owners() {
            let did = def_id.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let Some(name) = tcx.opt_item_name(did) else { continue };
            let name = name.to_string();
            if !matches!(
                name.as_str(),
                "vector_u64" | "vector_u8" | "recursive_node" | "recursive_vector" | "fake_vector"
            ) {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let parameter = body.local_decls[mir::Local::from_usize(1)].ty;
            let ty::TyKind::Adt(definition, _) = parameter.kind() else {
                panic!("fixture parameter must be an actual rustc ADT");
            };
            let real_vec = tcx.is_diagnostic_item(rustc_span::sym::Vec, definition.did());
            assert_eq!(
                real_vec,
                name.starts_with("vector_") || name == "recursive_vector",
                "only the actual std/alloc Vec may be recognized as Vec"
            );
            let layout = tcx
                .layout_of(body.typing_env(tcx).as_query_input(parameter))
                .expect("concrete fixture parameter has a compiler layout");
            let fields = &definition.non_enum_variant().fields;
            let shape = CompilerShape {
                fields: fields.iter().map(|field| field.name.to_string()).collect(),
                offsets: (0..fields.len())
                    .map(|i| layout.layout.fields().offset(i).bytes())
                    .collect(),
                size: layout.size.bytes(),
                align: layout.align.bytes(),
            };

            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            let logical_after = extract_function(tcx, body);
            // Compare complete extracted payloads and cache identities, not just
            // the root spelling. Both mode and per-body definition scope restore.
            assert_eq!(logical.content_hash(), logical_after.content_hash());
            assert_eq!(
                serde_json::to_vec(&logical).expect("logical input serializes"),
                serde_json::to_vec(&logical_after).expect("restored input serializes")
            );
            assert!(self.functions.insert(name, Modes { logical, faithful, shape }).is_none());
        }
        Compilation::Stop
    }
}

fn extract_modes() -> BTreeMap<String, Modes> {
    let mut callbacks = VecCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "faithful_vec_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=3".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    // Reuse the maintained matching-driver sysroot resolver. Missing std is a
    // real refusal, never a skipped/green test or an authored Vec replacement.
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile real std Vec fixture");
    assert_eq!(
        callbacks.functions.keys().map(String::as_str).collect::<Vec<_>>(),
        ["fake_vector", "recursive_node", "recursive_vector", "vector_u64", "vector_u8"]
    );
    callbacks.functions
}

fn resolve<'a>(function: &'a VerifiableFunction, ty: &'a Ty) -> &'a Ty {
    if trust_types::bare_datatype_marker_name(ty).is_some() {
        trust_types::datatype_marker_definition(&function.body.datatype_defs, ty)
            .expect("recursive logical marker has its own body-local definition")
    } else {
        ty
    }
}

fn parameter(function: &VerifiableFunction) -> &Ty {
    &function.body.locals.iter().find(|local| local.index == 1).expect("parameter").ty
}

fn physical_fields<'a>(modes: &'a Modes, suffix: &str) -> &'a [(String, Ty)] {
    let Ty::Adt { name, fields, variants, layout: Some(layout), adt_kind, .. } =
        &modes.faithful.body.return_ty
    else {
        panic!("physical {suffix} must be a complete struct, not Seq or an artificial cut");
    };
    assert!(name.ends_with(suffix), "wrong physical type {name}");
    assert_eq!(*adt_kind, Some(trust_types::AdtKind::Struct));
    assert!(variants.is_empty());
    assert_eq!(fields.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>(), modes.shape.fields);
    assert_eq!(layout.field_offsets, modes.shape.offsets);
    assert_eq!((layout.size, layout.align), (modes.shape.size, modes.shape.align));
    assert_eq!(parameter(&modes.faithful), &modes.faithful.body.return_ty);
    fields
}

fn assert_finite_physical(ty: &Ty, depth: usize) {
    assert!(depth < 64, "fixture physical graph must remain bounded");
    match ty {
        Ty::Adt { fields, variants, .. } => {
            for (_, child) in fields {
                assert_finite_physical(child, depth + 1);
            }
            for variant in variants {
                for (_, child) in &variant.fields {
                    assert_finite_physical(child, depth + 1);
                }
            }
        }
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
            assert_finite_physical(inner, depth + 1)
        }
        Ty::Tuple(fields) => {
            for child in fields {
                assert_finite_physical(child, depth + 1);
            }
        }
        Ty::Array { elem, .. } => assert_finite_physical(elem, depth + 1),
        Ty::Unit | Ty::Int { .. } | Ty::PtrSizedInt { .. } => {}
        other => panic!(
            "fixture must contain only physical fields, not a lost definition/Seq: {other:?}"
        ),
    }
}

#[test]
fn faithful_real_vec_has_compiler_fields_and_layout_while_logical_keeps_sequence() {
    let functions = extract_modes();
    for (name, width) in [("vector_u64", 64), ("vector_u8", 8)] {
        let modes = &functions[name];
        let Ty::Seq { elem, .. } = &modes.logical.body.return_ty else {
            panic!("logical std Vec must retain its sequence model");
        };
        assert_eq!(elem.as_ref(), &Ty::Int { width, signed: false });
        let fields = physical_fields(modes, "vec::Vec");
        // These field names are asserted ALSO against rustc above. A compiler
        // schema change must update this targeted RawVec+len regression openly.
        assert_eq!(
            fields.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(),
            ["buf", "len"]
        );
        assert!(matches!(&fields[0].1, Ty::Adt { name, .. } if name.ends_with("raw_vec::RawVec")));
        assert_eq!(fields[1].1, Ty::PtrSizedInt { signed: false });
        assert_finite_physical(&modes.faithful.body.return_ty, 0);
        assert!(modes.faithful.body.datatype_defs.is_empty());
    }
    assert_ne!(
        functions["vector_u64"].logical.body.return_ty,
        functions["vector_u8"].logical.body.return_ty,
        "logical element identity is retained"
    );
}

#[test]
fn faithful_recursive_vec_discovery_walk_matches_physical_rawvec_fields() {
    let functions = extract_modes();
    let modes = &functions["recursive_node"];
    let Ty::Adt { fields, .. } = resolve(&modes.logical, &modes.logical.body.return_ty) else {
        panic!("logical Node remains a struct containing a sequence");
    };
    let Ty::Seq { elem, .. } = &fields[0].1 else { panic!("logical children remain Seq<Node>") };
    let Ty::Adt { name, .. } = resolve(&modes.logical, elem) else {
        panic!("logical recursive Node definition")
    };
    assert!(name.ends_with("Node"));
    assert!(
        !modes.logical.body.datatype_defs.is_empty(),
        "logical recursion requires a real definition"
    );

    let physical = physical_fields(modes, "Node");
    assert_eq!(physical[0].0, "children");
    assert!(matches!(&physical[0].1, Ty::Adt { name, .. } if name.ends_with("vec::Vec")));
    // Current real RawVec<T> stores T only in fieldless PhantomData, not the
    // pointer (RawVecInner has Unique<u8>). This physical graph is acyclic.
    // Changing conversion alone but leaving discovery's Vec->T shortcut would
    // introduce an artificial Node cut; this assertion catches that mismatch.
    for name in ["recursive_node", "recursive_vector"] {
        let faithful = &functions[name].faithful;
        assert!(faithful.body.datatype_defs.is_empty(), "no logical Vec cycle in physical {name}");
        assert_finite_physical(&faithful.body.return_ty, 0);
        assert_eq!(parameter(faithful), &faithful.body.return_ty);
    }
}

#[test]
fn user_vec_lookalike_never_receives_std_sequence_semantics() {
    let functions = extract_modes();
    let modes = &functions["fake_vector"];
    let Ty::Adt { name, fields, .. } = &modes.logical.body.return_ty else {
        panic!("user-defined fake::Vec must not become Seq");
    };
    assert!(name.ends_with("fake::Vec"));
    assert_eq!(
        fields.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(),
        ["payload", "stamp"]
    );
    assert_eq!(fields[0].1, Ty::Int { width: 64, signed: false });
    assert_eq!(fields[1].1, Ty::Int { width: 8, signed: false });
    let physical = physical_fields(modes, "fake::Vec");
    assert_eq!(physical, fields.as_slice());
    assert_finite_physical(&modes.faithful.body.return_ty, 0);
}
