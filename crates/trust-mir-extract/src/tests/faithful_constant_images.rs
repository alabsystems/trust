// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compiler-owned diagnostic constant capture. These tests do not establish
//! runtime LazyLock/Vec semantics, executable lowering, or proof authority.

use rustc_middle::mir::interpret::GlobalAlloc;
use rustc_middle::mir::visit::Visitor;
use trust_types::{ConstantImageMemory, ConstantImageNode, ConstantImageRoot, ConstantMemoryImage};

use super::*;
use crate::constant_image::{MemoryImageScope, extract_memory_image};

const FIXTURE_PATH: &str = "faithful_constant_images_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

static NAME_NAT: std::sync::LazyLock<[u64; 4]> =
    std::sync::LazyLock::new(|| [1, 2, 3, 4]);
static NAME_STRING: std::sync::LazyLock<[u64; 4]> =
    std::sync::LazyLock::new(|| [5, 6, 7, 8]);

#[inline(never)]
pub fn consume(name: &[u64; 4], levels: Vec<u64>) -> u64 {
    name[0].wrapping_add(levels.len() as u64)
}

pub fn choose(flag: bool) -> u64 {
    if flag {
        consume(&NAME_NAT, Vec::new())
    } else {
        consume(&NAME_STRING, Vec::new())
    }
}

pub fn other() -> &'static std::sync::LazyLock<[u64; 4]> { &NAME_NAT }

static TOO_MANY_BYTES: [u8; 65_537] = [0; 65_537];
pub fn large() -> &'static [u8; 65_537] { &TOO_MANY_BYTES }

fn initialize() -> u64 { 9 }
static TOO_MANY_RELOCATIONS: [fn() -> u64; 1025] = [initialize; 1025];
pub fn many() -> &'static [fn() -> u64; 1025] { &TOO_MANY_RELOCATIONS }
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
            Err(io::Error::other("unexpected constant-image fixture source path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported in constant-image fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct Constants<'tcx> {
    values: Vec<mir::ConstOperand<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for Constants<'tcx> {
    fn visit_const_operand(
        &mut self,
        constant: &mir::ConstOperand<'tcx>,
        _location: mir::Location,
    ) {
        self.values.push(constant.clone());
    }
}

fn constants<'tcx>(body: &mir::Body<'tcx>) -> Vec<mir::ConstOperand<'tcx>> {
    let mut visitor = Constants::default();
    // Only constants actually used in the optimized blocks, not required_consts
    // retained solely for compile-time diagnostics after dead-code elimination.
    for (block, data) in body.basic_blocks.iter_enumerated() {
        visitor.visit_basic_block_data(block, data);
    }
    visitor.values
}

/// The static allocation `constant` points at, if it is a reference to a static.
fn static_allocation<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
) -> Option<rustc_middle::mir::interpret::AllocId> {
    let mir::Const::Val(mir::ConstValue::Scalar(scalar), _) = constant.const_ else {
        return None;
    };
    let pointer = scalar.to_pointer(&tcx);
    let (Some(provenance), _) = pointer.into_raw_parts() else { return None };
    matches!(tcx.try_get_global_alloc(provenance.alloc_id()), Some(GlobalAlloc::Static(_)))
        .then(|| provenance.alloc_id())
}

fn static_constant<'tcx>(tcx: TyCtxt<'tcx>, constant: &mir::ConstOperand<'tcx>) -> bool {
    static_allocation(tcx, constant).is_some()
}

fn rawvec_constant(tcx: TyCtxt<'_>, constant: &mir::ConstOperand<'_>) -> bool {
    let mir::Const::Val(mir::ConstValue::Indirect { .. }, ty) = constant.const_ else {
        return false;
    };
    matches!(ty.kind(), ty::TyKind::Adt(def, _) if crate::safe_def_path_str(tcx, def.did()).ends_with("raw_vec::RawVec"))
}

fn memory_root(image: &ConstantMemoryImage) -> (u32, &ConstantImageMemory) {
    let ConstantImageRoot::Indirect { allocation_id, offset_bytes: 0 } = image.root else {
        panic!("real RawVec buffer is an indirect root at offset zero");
    };
    let Some(ConstantImageNode::Memory(memory)) = image.nodes.get(&allocation_id) else {
        panic!("real RawVec root names ordinary memory");
    };
    (allocation_id, memory)
}

fn pointer_root_id(image: &ConstantMemoryImage) -> u32 {
    let ConstantImageRoot::Pointer(pointer) = &image.root else {
        panic!("static reference must retain pointer provenance");
    };
    assert_eq!(pointer.offset_bytes, 0);
    pointer.allocation_id
}

fn check_static_images(images: &[ConstantMemoryImage]) {
    assert_eq!(images.len(), 2, "both real LazyLock static operands survive optimized MIR");
    assert_ne!(pointer_root_id(&images[0]), pointer_root_id(&images[1]));
    let mut definitions = BTreeSet::new();
    let mut functions = Vec::new();
    for image in images {
        let ConstantImageNode::Static {
            definition,
            declared_mutable,
            freeze,
            thread_local,
            foreign,
            initializer,
        } = &image.nodes[&pointer_root_id(image)]
        else {
            panic!("reference points to a named static, not its initializer allocation");
        };
        assert!(!declared_mutable && !freeze && !thread_local && !foreign);
        assert!(initializer.mutable, "LazyLock interior mutability must remain visible");
        assert!(
            initializer.bytes.iter().any(Option::is_none),
            "unused union storage stays uninitialized"
        );
        assert_eq!(initializer.bytes.len() as u64, initializer.layout.size_bytes);
        assert!(
            definition.def_path.ends_with("NAME_NAT")
                || definition.def_path.ends_with("NAME_STRING")
        );
        assert!(definitions.insert(definition.def_path.clone()));
        assert_eq!(
            initializer.relocations.len(),
            1,
            "LazyLock initializer holds one function pointer"
        );
        let relocation = &initializer.relocations[0];
        let ConstantImageNode::Function {
            definition,
            instance_fingerprint,
            instance_debug,
            callee_identity,
        } = &image.nodes[&relocation.pointer.allocation_id]
        else {
            panic!("LazyLock initializer relocation preserves its callable instance");
        };
        assert!(!definition.def_path.is_empty() && !instance_debug.is_empty());
        functions.push((relocation.pointer.allocation_id, *instance_fingerprint, *callee_identity));
        assert_eq!(image.nodes.len(), 2, "static plus function is its complete fixture closure");
    }
    assert_ne!(functions[0].0, functions[1].0, "distinct compiler function allocation identities");
    assert_ne!(
        functions[0].1, functions[1].1,
        "different closure shims retain full instance identity"
    );
    assert_ne!(functions[0].2, functions[1].2, "different shim arguments retain callee identity");
}

fn check_rawvec_images(images: &[ConstantMemoryImage]) {
    assert_eq!(images.len(), 2, "both real empty Vec buffer operands must be measured");
    let (left_id, left) = memory_root(&images[0]);
    let (right_id, right) = memory_root(&images[1]);
    assert_ne!(left_id, right_id, "equal bytes do not merge separate compiler allocations");
    assert_eq!(left, right, "fixture intentionally carries identical bytes and allocation shape");
    assert!(left.bytes.iter().all(Option::is_some));
    assert!(left.relocations.is_empty(), "dangling integer pointers have NO allocation provenance");
    assert_eq!(images[0].nodes.len(), 1);
    assert_eq!(images[1].nodes.len(), 1);
    assert_eq!(images[0].ty_fingerprint, images[1].ty_fingerprint);
    // This test runs against the matching host compiler. For its 64-bit target,
    // the actual empty u64 Vec is cap=0 and the non-null dangling address 0x8.
    if images[0].target.pointer_size_bytes == 8 {
        assert_eq!(left.bytes.len(), 16);
        let mut expected = vec![Some(0); 16];
        let offset = if images[0].target.little_endian { 8 } else { 15 };
        expected[offset] = Some(8);
        assert_eq!(left.bytes, expected, "0x8 must survive; never fabricated null/allocation");
    }
}

#[derive(Default)]
struct ImageCallbacks {
    checked: bool,
}

impl rustc_driver::Callbacks for ImageCallbacks {
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
                matches!(name.as_str(), "choose" | "other" | "large" | "many")
                    .then(|| (name, tcx.optimized_mir(did)))
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(bodies.len(), 4);
        let body = bodies["choose"];
        let typing_env = body.typing_env(tcx);
        let used = constants(body);
        // Every operand that references a static, then ONE per distinct static.
        // The fixture's property is two DISTINCT statics, not two operands: with
        // the MIR inliner on, `<LazyLock as Deref>::deref` and `LazyLock::force`
        // are inlined into `choose`, `force` captures the reference in its
        // closure, and GVN propagates the constant into that closure aggregate.
        // Measured 2026-09-30 (optimized MIR of `choose`, this fixture, the
        // matching driver and sysroot): four operands, two per static,
        // `_3 = const {alloc1}` and `{closure} {{ 0: const {alloc1} }}`. Counting
        // operands made this test fail on an optimization detail; every repeat
        // is held to the first operand's image below instead.
        let static_operands =
            used.iter().filter(|constant| static_constant(tcx, constant)).collect::<Vec<_>>();
        let mut statics: Vec<&mir::ConstOperand<'tcx>> = Vec::new();
        for &operand in &static_operands {
            let allocation = static_allocation(tcx, operand);
            if !statics.iter().any(|seen| static_allocation(tcx, seen) == allocation) {
                statics.push(operand);
            }
        }
        let buffers =
            used.iter().filter(|constant| rawvec_constant(tcx, constant)).collect::<Vec<_>>();
        assert_eq!(statics.len(), 2, "fixture must exercise both actual static references");
        assert_eq!(buffers.len(), 2, "fixture must exercise both actual RawVec constants");

        // Check the integrated extraction path and logical mode restoration.
        let logical_before = extract_function(tcx, body);
        let faithful = extract_function_faithful(tcx, body);
        let logical_after = extract_function(tcx, body);
        assert_eq!(logical_before.content_hash(), logical_after.content_hash());
        assert_eq!(
            serde_json::to_vec(&logical_before).unwrap(),
            serde_json::to_vec(&logical_after).unwrap()
        );
        assert!(!logical_before.body.contains_memory_image());
        assert!(faithful.body.contains_memory_image(), "faithful fallback must actually be wired");
        assert!(!crate::ty_convert::faithful_scalars());
        assert!(
            extract_memory_image(tcx, statics[0], typing_env).unwrap_err().contains("faithful")
        );

        let _faithful = crate::ty_convert::FaithfulScalarsGuard::enable();
        assert!(extract_memory_image(tcx, statics[0], typing_env).unwrap_err().contains("scope"));
        let images = {
            let _scope = MemoryImageScope::begin(tcx, body);
            let images = statics
                .iter()
                .chain(&buffers)
                .map(|constant| {
                    extract_memory_image(tcx, constant, typing_env)
                        .expect("actual fixture image is representable")
                })
                .collect::<Vec<_>>();
            check_static_images(&images[..2]);
            check_rawvec_images(&images[2..]);
            // A repeated reference to one static (the inlined closure's capture)
            // images exactly as the first: same root, same closure, same IDs.
            for &operand in &static_operands {
                let allocation = static_allocation(tcx, operand);
                let first = statics
                    .iter()
                    .position(|seen| static_allocation(tcx, seen) == allocation)
                    .expect("every static operand has a first occurrence");
                assert_eq!(
                    extract_memory_image(tcx, operand, typing_env)
                        .expect("every static operand is representable"),
                    images[first],
                    "a repeated reference to one static must image identically"
                );
            }
            let repeated =
                extract_memory_image(tcx, statics[0], typing_env).expect("same operand repeats");
            assert_eq!(
                images[0], repeated,
                "same body scope retains allocation IDs and complete closure"
            );
            {
                let _nested = MemoryImageScope::begin(tcx, bodies["other"]);
                let nested =
                    extract_memory_image(tcx, statics[0], typing_env).expect("nested scope image");
                assert_ne!(images[0].owner.def_path_hash, nested.owner.def_path_hash);
                assert_eq!(pointer_root_id(&nested), 0, "fresh body starts its own namespace");
            }
            assert_eq!(
                images[0],
                extract_memory_image(tcx, statics[0], typing_env).unwrap(),
                "nested scope restores outer IDs"
            );
            images
        };
        assert!(extract_memory_image(tcx, statics[0], typing_env).unwrap_err().contains("scope"));
        for image in &images {
            let constant = ConstValue::MemoryImage(Box::new(image.clone()));
            assert!(
                codegen_const_issue(&constant).is_some(),
                "diagnostic image is not executable codegen"
            );
            let nested = ConstValue::struct_scalar_fields_ref("Forged", vec![constant]);
            assert!(nested.contains_memory_image());
            assert!(
                codegen_const_issue(&nested).is_some(),
                "nesting cannot launder an image into codegen"
            );
        }

        // Compiler source independently determines every ordinary allocation byte
        // and initialization bit; do not merely compare two producer outputs.
        for (constant, image) in buffers.iter().zip(&images[2..]) {
            let mir::Const::Val(mir::ConstValue::Indirect { alloc_id, .. }, _) = constant.const_
            else {
                unreachable!()
            };
            let Some(GlobalAlloc::Memory(allocation)) = tcx.try_get_global_alloc(alloc_id) else {
                panic!("real memory")
            };
            let allocation = allocation.inner();
            let observed = allocation
                .inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len())
                .iter()
                .enumerate()
                .map(|(index, byte)| {
                    allocation.init_mask().get(rustc_abi::Size::from_bytes(index)).then_some(*byte)
                })
                .collect::<Vec<_>>();
            assert_eq!(memory_root(image).1.bytes, observed);
        }

        // Frozen CTFE must refuse rather than evaluating a local static. Fresh
        // scopes demonstrate that a refusal is not inherited by the next body.
        {
            let _scope = MemoryImageScope::begin(tcx, body);
            let _freeze = crate::ctfe_reentrancy::enter();
            assert!(
                extract_memory_image(tcx, statics[0], typing_env).unwrap_err().contains("frozen")
            );
        }
        {
            let _scope = MemoryImageScope::begin(tcx, body);
            assert!(extract_memory_image(tcx, statics[0], typing_env).is_ok());
        }
        {
            let _scope = MemoryImageScope::begin(tcx, body);
            let mut unevaluated = buffers[0].clone();
            unevaluated.const_ = mir::Const::Unevaluated(
                mir::UnevaluatedConst::new(body.source.def_id(), ty::GenericArgs::empty()),
                unevaluated.const_.ty(),
            );
            // Deliberately non-evaluable input: it must be refused by spelling
            // before any CTFE query is attempted on this ordinary function.
            assert!(
                extract_memory_image(tcx, &unevaluated, typing_env)
                    .unwrap_err()
                    .contains("already evaluated Const::Val")
            );
        }
        {
            let _scope = MemoryImageScope::begin(tcx, body);
            let mut missing = buffers[0].clone();
            let mir::Const::Val(mir::ConstValue::Indirect { offset, .. }, ty) = missing.const_
            else {
                unreachable!()
            };
            // This reserved ID is intentionally NOT published as a query result
            // or MIR value. It is solely an adversarial extractor input.
            missing.const_ = mir::Const::Val(
                mir::ConstValue::Indirect { alloc_id: tcx.reserve_alloc_id(), offset },
                ty,
            );
            assert!(
                extract_memory_image(tcx, &missing, typing_env)
                    .unwrap_err()
                    .contains("missing compiler allocation")
            );
        }
        for (name, budget) in [("large", "bytes"), ("many", "relocations")] {
            let selected = bodies[name];
            let used = constants(selected);
            let constant = used
                .iter()
                .find(|constant| static_constant(tcx, constant))
                .expect("budget fixture returns a static ref");
            let _scope = MemoryImageScope::begin(tcx, selected);
            let error = extract_memory_image(tcx, constant, selected.typing_env(tcx)).unwrap_err();
            assert!(
                error.contains("budget") && error.contains(budget),
                "actual compiler allocation must hit {budget} bound: {error}"
            );
        }

        // Controlled compiler allocations, not hand-authored public-model images:
        // equal bytes under distinct real AllocIds must consume distinct nodes.
        {
            let _scope = MemoryImageScope::begin(tcx, body);
            let mut constant = buffers[0].clone();
            let mir::Const::Val(mir::ConstValue::Indirect { alloc_id, offset }, ty) =
                constant.const_
            else {
                unreachable!()
            };
            let Some(GlobalAlloc::Memory(allocation)) = tcx.try_get_global_alloc(alloc_id) else {
                panic!("real memory")
            };
            for _ in 0..64 {
                let id = tcx.reserve_and_set_memory_alloc(allocation);
                constant.const_ =
                    mir::Const::Val(mir::ConstValue::Indirect { alloc_id: id, offset }, ty);
                extract_memory_image(tcx, &constant, typing_env).expect("within exact node bound");
            }
            let id = tcx.reserve_and_set_memory_alloc(allocation);
            constant.const_ =
                mir::Const::Val(mir::ConstValue::Indirect { alloc_id: id, offset }, ty);
            assert!(
                extract_memory_image(tcx, &constant, typing_env).unwrap_err().contains("64 nodes")
            );
        }
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
fn faithful_constant_images_preserve_real_storage_and_refuse_incomplete_capture() {
    let mut callbacks = ImageCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "faithful_constant_images_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Copt-level=3".into(),
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
    assert!(result.is_ok(), "failed to compile real constant-image fixture");
    assert!(callbacks.checked, "callback must execute every control");
}
