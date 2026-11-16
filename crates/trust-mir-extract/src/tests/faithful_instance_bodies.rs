// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Real compiler instance selection and monomorphized body capture. These are
//! identity/extraction controls, not proofs of the captured callees' behavior.

use trust_types::{ConstantImageNode, ConstantMemoryImage};

use super::*;
use crate::instance_body::{
    FaithfulInstanceError, extract_faithful_body_with_function_allocations,
    extract_instance_faithful, faithful_instance_descriptor, resolve_faithful_call,
};

const FIXTURE_PATH: &str = "faithful_instance_bodies_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

#[inline(never)]
pub fn repeat<T: Copy, const N: usize>(value: T) -> [T; N] { [value; N] }
pub fn concrete_u32(value: u32) -> [u32; 2] { repeat::<u32, 2>(value) }
pub fn concrete_u64(value: u64) -> [u64; 3] { repeat::<u64, 3>(value) }

pub trait Echo { fn echo(self) -> u32; }
impl Echo for u32 {
    #[inline(never)]
    fn echo(self) -> u32 { self.wrapping_add(7) }
}
pub fn concrete_trait(value: u32) -> u32 { <u32 as Echo>::echo(value) }
pub fn unresolved<T: Echo>(value: T) -> u32 { <T as Echo>::echo(value) }
pub fn indirect(f: fn(u32) -> u32, value: u32) -> u32 { f(value) }

extern "C" { fn foreign_value(value: u32) -> u32; }
pub unsafe fn foreign(value: u32) -> u32 { foreign_value(value) }
pub fn plain(value: u64) -> u64 { value }

static INITIALIZER: std::sync::LazyLock<[u64; 4]> =
    std::sync::LazyLock::new(|| [1, 2, 3, 4]);
pub fn initializer() -> &'static std::sync::LazyLock<[u64; 4]> { &INITIALIZER }
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
            Err(io::Error::other("unexpected faithful instance fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported in instance fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

fn only_call<'a, 'tcx>(body: &'a mir::Body<'tcx>) -> &'a mir::Operand<'tcx> {
    let calls = body
        .basic_blocks
        .iter()
        .filter_map(|block| match &block.terminator().kind {
            mir::TerminatorKind::Call { func, .. } => Some(func),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1, "selected real fixture call must survive optimization");
    calls[0]
}

fn assert_concrete(body: &mir::Body<'_>) {
    assert!(
        !body.has_non_region_param(),
        "captured body must substitute type AND const parameters"
    );
    assert!(!body.has_non_region_infer(), "no inference variables in captured body");
    assert!(!body.has_non_region_placeholders(), "no placeholder parameters in captured body");
}

// Inspect the public serialized model, not the producer's allocation list. This
// independently requires every returned allocation edge to exist in an emitted
// MemoryImage; reserved-but-refused image allocations cannot count as edges.
fn emitted_function_nodes(function: &VerifiableFunction) -> BTreeMap<u32, ConstantImageNode> {
    fn collect(value: &serde_json::Value, result: &mut BTreeMap<u32, ConstantImageNode>) {
        match value {
            serde_json::Value::Object(fields) => {
                if let Some(image) = fields.get("MemoryImage") {
                    let image: ConstantMemoryImage =
                        serde_json::from_value(image.clone()).expect("typed emitted memory image");
                    for (id, node) in image.nodes {
                        if matches!(node, ConstantImageNode::Function { .. }) {
                            if let Some(previous) = result.insert(id, node.clone()) {
                                assert_eq!(
                                    previous, node,
                                    "one body allocation ID has one identity"
                                );
                            }
                        }
                    }
                } else {
                    for field in fields.values() {
                        collect(field, result);
                    }
                }
            }
            serde_json::Value::Array(values) => {
                for value in values {
                    collect(value, result);
                }
            }
            _ => {}
        }
    }
    let mut result = BTreeMap::new();
    collect(&serde_json::to_value(function).expect("serializable faithful body"), &mut result);
    result
}

#[derive(Default)]
struct InstanceCallbacks {
    checked: bool,
}

impl rustc_driver::Callbacks for InstanceCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        let bodies = tcx
            .hir_body_owners()
            .filter_map(|owner| {
                let did = owner.to_def_id();
                if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                    return None;
                }
                let name = tcx.opt_item_name(did)?.to_string();
                matches!(
                    name.as_str(),
                    "repeat"
                        | "concrete_u32"
                        | "concrete_u64"
                        | "concrete_trait"
                        | "unresolved"
                        | "indirect"
                        | "foreign"
                        | "plain"
                        | "initializer"
                )
                .then(|| (name, tcx.optimized_mir(did)))
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(bodies.len(), 9);
        assert!(bodies["repeat"].has_non_region_param(), "fixture really starts polymorphic");

        let mut monomorphizations = Vec::new();
        for (caller, scalar, length) in
            [("concrete_u32", tcx.types.u32, 2_usize), ("concrete_u64", tcx.types.u64, 3_usize)]
        {
            let body = bodies[caller];
            let operand = only_call(body);
            let (did, args) = operand.const_fn_def().expect("real concrete generic FnDef");
            assert_eq!(tcx.item_name(did).as_str(), "repeat");
            let expected =
                ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), did, args)
                    .expect("compiler resolution succeeds")
                    .expect("concrete generic instance");
            let resolved = resolve_faithful_call(tcx, body, operand).expect("resolve direct call");
            assert_eq!(resolved.instance, expected);
            assert_eq!(resolved.syntactic_definition, crate::constant_image::definition(tcx, did));
            assert_eq!(
                resolved.syntactic_identity,
                crate::convert::callee_identity_for(tcx, did, args).expect("concrete identity")
            );
            let extracted =
                extract_instance_faithful(tcx, expected).expect("capture concrete body");
            assert_eq!(extracted.instance, expected);
            assert_eq!(extracted.mir.source.instance, expected.def);
            assert_concrete(&extracted.mir);
            assert_eq!(extracted.mir.local_decls[mir::Local::from_usize(1)].ty, scalar);
            let ty::TyKind::Array(element, count) = extracted.mir.return_ty().kind() else {
                panic!("monomorphized return must remain the actual compiler array type")
            };
            assert_eq!(*element, scalar);
            assert_eq!(count.try_to_target_usize(tcx), Some(length as u64));
            let model_scalar = if length == 2 { Ty::u32() } else { Ty::u64() };
            assert_eq!(
                extracted.function.body.return_ty,
                Ty::Array { elem: Box::new(model_scalar), len: length as u64 }
            );
            assert!(
                extracted.function.body.blocks.iter().any(|block| {
                    block.stmts.iter().any(|statement| {
                        matches!(statement,
                        Statement::Assign { rvalue: Rvalue::Repeat(_, count), .. }
                            if *count == length)
                    })
                }),
                "body operands, not just the return signature, retain the substituted const"
            );
            assert!(extracted.allocation_functions.is_empty());
            assert!(!extracted.function.body.contains_memory_image());
            monomorphizations.push((
                faithful_instance_descriptor(tcx, expected).expect("exact generic descriptor"),
                extracted.function.content_hash(),
            ));
        }
        assert_ne!(monomorphizations[0].0, monomorphizations[1].0);
        assert_ne!(monomorphizations[0].1, monomorphizations[1].1);

        // Keep the written trait method and the selected impl body distinct.
        let trait_body = bodies["concrete_trait"];
        let trait_operand = only_call(trait_body);
        let (trait_method, args) = trait_operand.const_fn_def().expect("written trait call");
        assert!(tcx.trait_of_assoc(trait_method).is_some());
        let selected = resolve_faithful_call(tcx, trait_body, trait_operand)
            .expect("concrete trait method resolves to its implementation");
        assert_ne!(selected.instance.def_id(), trait_method);
        assert_eq!(
            selected.syntactic_definition,
            crate::constant_image::definition(tcx, trait_method)
        );
        assert_eq!(
            selected.syntactic_identity,
            crate::convert::callee_identity_for(tcx, trait_method, args).unwrap()
        );
        let implementation = extract_instance_faithful(tcx, selected.instance).expect("impl MIR");
        assert_eq!(implementation.mir.source.def_id(), selected.instance.def_id());
        assert_concrete(&implementation.mir);

        let plain = bodies["plain"];
        let plain_instance = ty::Instance::new_raw(plain.source.def_id(), ty::GenericArgs::empty());
        let direct = extract_function_faithful(tcx, plain);
        let captured = extract_instance_faithful(tcx, plain_instance).expect("plain item body");
        assert_eq!(
            serde_json::to_value(&direct).unwrap(),
            serde_json::to_value(&captured.function).unwrap(),
            "image-free non-generic extraction must retain existing faithful output"
        );

        assert!(matches!(
            resolve_faithful_call(tcx, bodies["indirect"], only_call(bodies["indirect"])),
            Err(FaithfulInstanceError::NotDirectCall)
        ));
        assert!(matches!(
            resolve_faithful_call(tcx, bodies["unresolved"], only_call(bodies["unresolved"])),
            Err(FaithfulInstanceError::NonConcrete)
        ));
        let generic = bodies["repeat"].source.def_id();
        let unresolved =
            ty::Instance::new_raw(generic, ty::GenericArgs::identity_for_item(tcx, generic));
        assert!(matches!(
            extract_instance_faithful(tcx, unresolved),
            Err(FaithfulInstanceError::NonConcrete)
        ));
        let (foreign, foreign_args) = only_call(bodies["foreign"]).const_fn_def().unwrap();
        assert!(tcx.is_foreign_item(foreign));
        assert!(!tcx.is_mir_available(foreign));
        let foreign_instance = ty::Instance::new_raw(foreign, foreign_args);
        assert!(matches!(
            extract_instance_faithful(tcx, foreign_instance),
            Err(FaithfulInstanceError::ForeignItem)
        ));
        {
            let _frozen = crate::ctfe_reentrancy::enter();
            assert!(matches!(
                resolve_faithful_call(tcx, trait_body, trait_operand),
                Err(FaithfulInstanceError::Frozen)
            ));
            assert!(matches!(
                extract_instance_faithful(tcx, plain_instance),
                Err(FaithfulInstanceError::Frozen)
            ));
        }
        assert!(extract_instance_faithful(tcx, plain_instance).is_ok(), "freeze must restore");

        let (initializer, functions) =
            extract_faithful_body_with_function_allocations(tcx, bodies["initializer"]);
        assert!(initializer.body.contains_memory_image());
        let nodes = emitted_function_nodes(&initializer);
        assert_eq!(nodes.len(), 1, "actual static has exactly one initializer function relocation");
        assert_eq!(
            functions.len(),
            nodes.len(),
            "no omitted or invented function allocation edges"
        );
        for (id, instance) in functions {
            let instance = instance.expect("emitted live allocation resolves without mismatch");
            assert!(matches!(instance.def, ty::InstanceKind::Shim(_)), "real closure call shim");
            let descriptor = faithful_instance_descriptor(tcx, instance).expect("shim descriptor");
            assert_eq!(nodes.get(&id), Some(&descriptor), "edge names emitted allocation identity");
            // Hold the defining item and substitutions fixed: a kind-blind
            // fingerprint would incorrectly alias this shim with an item.
            let same_item = ty::Instance::new_raw(instance.def_id(), instance.args);
            let item_descriptor = faithful_instance_descriptor(tcx, same_item)
                .expect("concrete descriptor does not claim that item MIR exists");
            let (
                ConstantImageNode::Function {
                    definition: shim_definition,
                    instance_fingerprint: shim_fingerprint,
                    callee_identity: shim_identity,
                    ..
                },
                ConstantImageNode::Function {
                    definition: item_definition,
                    instance_fingerprint: item_fingerprint,
                    callee_identity: item_identity,
                    ..
                },
            ) = (&descriptor, &item_descriptor)
            else {
                panic!("callable descriptors retain typed function nodes")
            };
            assert_eq!(shim_definition, item_definition);
            assert_eq!(shim_identity, item_identity, "def+args alone do not distinguish kind");
            assert_ne!(shim_fingerprint, item_fingerprint, "full instance kind is load-bearing");
            assert!(!tcx.is_mir_available(same_item.def_id()), "FnOnce item has no default MIR");
            assert!(matches!(
                extract_instance_faithful(tcx, same_item),
                Err(FaithfulInstanceError::MirUnavailable)
            ));
            let shim =
                extract_instance_faithful(tcx, instance).expect("actual generated shim body");
            assert_eq!(shim.instance, instance);
            assert_eq!(shim.mir.source.instance, instance.def, "never replace shim with item MIR");
            assert_concrete(&shim.mir);
            assert!(!shim.mir.basic_blocks.is_empty());
            assert!(shim.function.body.arg_count > 0, "FnOnce shim keeps its callable signature");
        }
        assert!(!crate::ty_convert::faithful_scalars(), "all capture guards restore caller mode");
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
fn faithful_instance_bodies_bind_real_monomorphizations_and_refuse_unavailable_calls() {
    let mut callbacks = InstanceCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "faithful_instance_bodies_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Copt-level=0".into(),
        "-Zmir-opt-level=0".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile real instance-selection fixture");
    assert!(callbacks.checked, "callback must execute every selection and refusal control");
}
