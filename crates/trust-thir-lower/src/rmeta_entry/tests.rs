//! Unit tests for the per-definition rmeta entry builder (step 6.1). TyCtxt-free: the rustc half
//! (`RustcNames`: symbols over re-derived instances, `DefPathHash` spellings) only computes the
//! inputs these pin, and is exercised end to end by `tests/run-make/trust-ir-rmeta-entry-roundtrip`.

use std::collections::{BTreeMap, BTreeSet};

use rustc_span::DUMMY_SP;
use rustc_span::def_id::{CrateNum, DefId, DefIndex};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    ProofAnnotation, Ty, ValueId,
};

use super::*;
use crate::effect_conservation::{MemRoot, MirEffect};
use crate::lineage::{ConcreteCalleeKey, ConcreteInstanceKind, DefinitionIdentity};

fn def(index: u32) -> DefId {
    DefId { krate: CrateNum::from_u32(0), index: DefIndex::from_u32(index) }
}

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn node_r(inst: Inst, r: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(r))
}

/// A one-function per-body module: `fn(i32) -> i32` whose entry block runs `body`.
fn per_body_module(body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("dep");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "dep::mix", ty, BlockId::new(0));
    f.calling_conv = trust_ir::CallingConv::Rust;
    let mut b = Block::new(BlockId::new(0)).with_param(v(0), Ty::I32);
    b.body = body;
    f.blocks = vec![b];
    module.functions.push(f);
    module
}

fn ret(value: u32) -> InstrNode {
    node(Inst::Return { values: vec![v(value)] })
}

/// `x ^ 0x5a5a_5a5a`, the design's monomorphic subject.
fn mix_body() -> Vec<InstrNode> {
    vec![
        node_r(Inst::Const { ty: Ty::I32, value: Constant::Int(0x5a5a_5a5a) }, 1),
        node_r(Inst::BinOp { op: trust_ir::BinOp::Xor, ty: Ty::I32, lhs: v(0), rhs: v(1) }, 2),
        ret(2),
    ]
}

/// The same body calling `FuncId(1)` once with its argument, returning the result.
fn calling_body() -> Vec<InstrNode> {
    vec![node_r(Inst::Call { callee: FuncId::new(1), args: vec![v(0)] }, 1), ret(1)]
}

fn callee(k: u32, def_index: u32) -> CalleeRef {
    let def_id = def(def_index);
    let definition = DefinitionIdentity::test_only(0xC0DE, def_index as u64);
    CalleeRef {
        func_id: FuncId::new(k),
        is_local: true,
        def_index,
        def_id,
        definition,
        concrete_key: Some(ConcreteCalleeKey::test_only(
            definition,
            ConcreteInstanceKind::Item,
            Vec::new(),
        )),
        def_path: format!("dep::callee{def_index}"),
        force_havoc: false,
        site_def_id: def_id,
        site_args: Some(Vec::new()),
        instance_args: Some(Vec::new()),
        ret_ty: Some(Ty::I32),
        ret_ty_conflict: false,
        abi: crate::calling_convention::FunctionAbi::RUST,
        params: crate::ParamSignature::Signed(vec![Ty::I32]),
    }
}

fn candidate(module: Module, callees: Vec<CalleeRef>) -> Candidate {
    let global_origins = vec![GlobalOrigin::BodyLocal; module.globals.len()];
    Candidate { module, callees, global_origins, body_kind: BodyKind::Fn, not_lowered: Vec::new() }
}

/// The local path the fixture's source file has on the "build machine", and its spelling in
/// metadata under `--remap-path-prefix=/build/dep=/REMAPPED`.
const LOCAL_FILE: &str = "/build/dep/src/lib.rs";
const REMAPPED_FILE: &str = "/REMAPPED/src/lib.rs";

/// Fixture names: the body is `_RNvCs_dep_mix`, callee `k` is `_RNvCs_dep_callee<k>`, a static
/// `def` is `_RNvCs_dep_static<index>`; any edge listed in `unnamed` has no symbol, any edge in
/// `track_caller` is `#[track_caller]`, and so is the body when `body_track_caller`. The source
/// map knows exactly [`LOCAL_FILE`], remapped to [`REMAPPED_FILE`].
struct Names {
    unnamed: BTreeSet<usize>,
    track_caller: BTreeSet<usize>,
    body_track_caller: bool,
}

fn names() -> Names {
    Names { unnamed: BTreeSet::new(), track_caller: BTreeSet::new(), body_track_caller: false }
}

impl EntryNames for Names {
    fn body_symbol(&self) -> Result<String, String> {
        Ok("_RNvCs_dep_mix".to_string())
    }
    fn body_abi(&self) -> crate::calling_convention::FunctionAbi {
        crate::calling_convention::FunctionAbi::RUST
    }
    fn body_requires_caller_location(&self) -> bool {
        self.body_track_caller
    }
    fn callee_symbol(&self, k: usize, _callee: &CalleeRef) -> Result<String, CalleeNameRefusal> {
        if self.unnamed.contains(&k) {
            Err(CalleeNameRefusal::Unnamed("a havoc edge".to_string()))
        } else if self.track_caller.contains(&k) {
            Err(CalleeNameRefusal::CallerLocation)
        } else {
            Ok(format!("_RNvCs_dep_callee{k}"))
        }
    }
    fn static_symbol(&self, def: DefId) -> Result<String, String> {
        Ok(format!("_RNvCs_dep_static{}", def.index.as_u32()))
    }
    fn file_name(&self, local: &str) -> Result<String, String> {
        if local == LOCAL_FILE {
            Ok(REMAPPED_FILE.to_string())
        } else {
            Err("the session's source map names no such file".to_string())
        }
    }
    fn target_info(&self) -> trust_ir::TargetInfo {
        target()
    }
}

fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "arm64-apple-macosx11.0.0".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

fn conserved(c: &Candidate) -> EntryInputs<'_> {
    EntryInputs {
        candidate: c,
        generic: false,
        clean_origin: false,
        verdict: VerdictInput::Classes(Vec::new()),
    }
}

#[test]
fn entry_is_the_body_conservation_judged_with_callees_named_by_symbol() {
    let c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let entry = build_entry_module(&conserved(&c), &names()).expect("a conserved body encodes");
    assert_eq!(entry.functions.len(), 2, "the body plus one declaration");
    let body = &entry.functions[0];
    assert_eq!(body.id, FuncId::new(0));
    assert_eq!(body.name, "_RNvCs_dep_mix", "the body is named by its link symbol");
    assert_eq!(body.calling_conv, trust_ir::CallingConv::Rust, "an entry states the real ABI");
    assert_eq!(
        body.blocks, c.module.functions[0].blocks,
        "the body's code is the judged per-body function, byte for byte"
    );
    let decl = &entry.functions[1];
    assert_eq!(decl.id, FuncId::new(1));
    assert_eq!(decl.name, "_RNvCs_dep_callee1", "a callee is declared by its link symbol");
    assert!(decl.blocks.is_empty(), "a callee is a declaration, never a body");
    assert_eq!(decl.linkage, Linkage::External);
    assert_eq!(decl.calling_conv, trust_ir::CallingConv::Rust);
    let sig = &entry.func_types[decl.ty.index() as usize];
    assert_eq!((sig.params.clone(), sig.returns.clone()), (vec![Ty::I32], vec![Ty::I32]));
    assert!(!sig.is_vararg, "a declaration is signed, never `(...)`");
    assert!(entry.target_info.is_some(), "stamped with its target, so it validates alone");
    assert!(trust_ir_build::validate_module(&entry).is_empty());
}

#[test]
fn internal_globals_travel_with_initializers_and_external_ones_as_declarations() {
    let global = |name: &str, linkage: Linkage, initializer: Option<Constant>| Global {
        name: name.to_string(),
        ty: Ty::I32,
        mutable: false,
        initializer,
        linkage,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    };
    let mut module = per_body_module(vec![
        node_r(Inst::GlobalAddr { global: GlobalId::new(0) }, 1),
        node_r(Inst::GlobalAddr { global: GlobalId::new(1) }, 2),
        node_r(Inst::Load { ty: Ty::I32, ptr: v(2), volatile: false, align: None }, 3),
        ret(3),
    ]);
    module.globals = vec![
        global("__trust_promoted_0", Linkage::Internal, Some(Constant::Int(7))),
        global("__trust_static_1__dep::LIMIT", Linkage::Internal, Some(Constant::Int(10))),
    ];
    let mut c = candidate(module, Vec::new());
    c.global_origins = vec![GlobalOrigin::BodyLocal, GlobalOrigin::Static(def(42))];
    let entry = build_entry_module(&conserved(&c), &names()).expect("encodes");
    let promoted = &entry.globals[0];
    assert_eq!(promoted.name, "__trust_promoted_0");
    assert_eq!(promoted.linkage, Linkage::Internal);
    assert_eq!(promoted.initializer, Some(Constant::Int(7)), "body-local data travels with it");
    let stat = &entry.globals[1];
    assert_eq!(stat.name, "_RNvCs_dep_static42", "a static is bound by its link symbol");
    assert_eq!(stat.linkage, Linkage::External);
    assert_eq!(stat.initializer, None, "a static is never copied: it has one address");
    // The census admits exactly that declaration: the instance lane's rule (no statics) refuses
    // the entry, and so does the entry's own rule when the global is not a static declaration.
    assert!(crate::instance_admission::instance_module_is_self_contained(&entry, 0).is_err());
    assert!(entry_is_self_contained(&entry, 0, &BTreeSet::new()).is_err());
    assert_eq!(
        entry_is_self_contained(&entry, 0, &[GlobalId::new(1)].into_iter().collect()),
        Ok(())
    );

    // A body-local global with no initializer cannot travel.
    let mut bad = c.clone();
    bad.module.globals[0].initializer = None;
    assert!(matches!(
        build_entry_module(&conserved(&bad), &names()),
        Err(EntryRefusal::UnnamedGlobal(_))
    ));
    // Nor one the producer left external.
    let mut bad = c.clone();
    bad.module.globals[0].linkage = Linkage::External;
    assert!(matches!(
        build_entry_module(&conserved(&bad), &names()),
        Err(EntryRefusal::UnnamedGlobal(_))
    ));
}

#[test]
fn every_refusal_reason_is_recorded_and_no_entry_is_written() {
    let base = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let refuse = |inputs: EntryInputs<'_>, names: &Names| -> EntryRefusal {
        build_entry_module(&inputs, names).expect_err("refused")
    };
    // (class, refusal) per row of design §4, each beside the conserved control above.
    let mut rows: Vec<(&str, EntryRefusal)> = Vec::new();
    rows.push((
        "template-pending",
        refuse(EntryInputs { generic: true, ..conserved(&base) }, &names()),
    ));
    let mut init = base.clone();
    init.body_kind = BodyKind::ConstInit;
    rows.push(("not-a-function", refuse(conserved(&init), &names())));
    rows.push((
        "clean-origin",
        refuse(EntryInputs { clean_origin: true, ..conserved(&base) }, &names()),
    ));
    let mut dirty = base.clone();
    dirty.not_lowered = vec!["symbolic".to_string()];
    rows.push(("not-lowered", refuse(conserved(&dirty), &names())));
    rows.push((
        "conservation-unchecked",
        refuse(
            EntryInputs {
                verdict: VerdictInput::Unchecked("did not run".to_string()),
                ..conserved(&base)
            },
            &names(),
        ),
    ));
    rows.push((
        "not-conserved",
        refuse(
            EntryInputs {
                verdict: VerdictInput::Classes(vec!["not-conserved(call)".to_string()]),
                ..conserved(&base)
            },
            &names(),
        ),
    ));
    let asserting = candidate(
        per_body_module(vec![
            node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
                .with_proof(ProofAnnotation::NoOverflow),
            ret(0),
        ]),
        Vec::new(),
    );
    rows.push(("unsited-panic", refuse(conserved(&asserting), &names())));
    let unnamed = Names { unnamed: [1].into_iter().collect(), ..names() };
    rows.push(("unnamed-callee", refuse(conserved(&base), &unnamed)));
    let track_caller_callee = Names { track_caller: [1].into_iter().collect(), ..names() };
    rows.push(("caller-location", refuse(conserved(&base), &track_caller_callee)));
    let track_caller_body = Names { body_track_caller: true, ..names() };
    rows.push(("caller-location", refuse(conserved(&base), &track_caller_body)));
    let mut unsigned = base.clone();
    unsigned.callees[0].params = crate::ParamSignature::Unsigned;
    rows.push(("unnamed-callee", refuse(conserved(&unsigned), &names())));
    let mut global = base.clone();
    global.global_origins = vec![GlobalOrigin::BodyLocal];
    rows.push(("unnamed-global", refuse(conserved(&global), &names())));
    let mut sparse = base.clone();
    sparse.callees[0].func_id = FuncId::new(2);
    rows.push(("invalid", refuse(conserved(&sparse), &names())));
    // A body with no link symbol of its own (a coroutine body read as a closure) is invalid, not
    // a callee the consumer cannot name.
    struct NoBodySymbol;
    impl EntryNames for NoBodySymbol {
        fn body_symbol(&self) -> Result<String, String> {
            Err("a closure definition of type kind Coroutine".to_string())
        }
        fn body_abi(&self) -> crate::calling_convention::FunctionAbi {
            crate::calling_convention::FunctionAbi::RUST
        }
        fn body_requires_caller_location(&self) -> bool {
            false
        }
        fn callee_symbol(&self, k: usize, callee: &CalleeRef) -> Result<String, CalleeNameRefusal> {
            names().callee_symbol(k, callee)
        }
        fn static_symbol(&self, def: DefId) -> Result<String, String> {
            names().static_symbol(def)
        }
        fn file_name(&self, local: &str) -> Result<String, String> {
            names().file_name(local)
        }
        fn target_info(&self) -> trust_ir::TargetInfo {
            target()
        }
    }
    rows.push((
        "invalid",
        build_entry_module(&conserved(&base), &NoBodySymbol).expect_err("refused"),
    ));
    // Step 6.5.1: one row per template class (a generic definition's row is the template
    // builder's, and it writes no byte either).
    let passing =
        template_record(template_candidate(calling_template_module(), vec![callee(1, 9)]));
    let row = |inputs: TemplateInputs<'_>, names: &Names| template_row(&inputs, names);
    rows.push((
        "template-pending",
        row(
            TemplateInputs { record: None, capture_on: false, ..template_inputs(&passing) },
            &names(),
        ),
    ));
    rows.push(("template-pending", row(template_inputs(&passing), &names())));
    let non_generic_closure =
        refused_template(CaptureRefusal::ClosureKind { kind: "closure", generic: false });
    rows.push(("template-pending", row(template_inputs(&non_generic_closure), &names())));
    let lane = refused_template(CaptureRefusal::Lane(vec![
        "parameter-dependent pointer metadata".to_string(),
    ]));
    rows.push(("template-unsupported", row(template_inputs(&lane), &names())));
    let closure_kind =
        refused_template(CaptureRefusal::ClosureKind { kind: "coroutine", generic: true });
    rows.push(("template-unsupported", row(template_inputs(&closure_kind), &names())));
    let proof_surface =
        template_record(template_candidate(proof_surface_template_module(), Vec::new()));
    rows.push(("template-unsupported", row(template_inputs(&proof_surface), &names())));
    let not_lowered = refused_template(CaptureRefusal::NotLowered(vec!["symbolic".to_string()]));
    rows.push(("not-lowered", row(template_inputs(&not_lowered), &names())));
    let unsited = refused_template(CaptureRefusal::UnsitedPanic(vec!["overflow"]));
    rows.push(("unsited-panic", row(template_inputs(&unsited), &names())));
    rows.push(("caller-location", row(template_inputs(&passing), &track_caller_body)));
    rows.push(("caller-location", row(template_inputs(&passing), &track_caller_callee)));
    rows.push(("unnamed-callee", row(template_inputs(&passing), &unnamed)));
    rows.push((
        "conservation-unchecked",
        row(
            TemplateInputs {
                verdict: VerdictInput::Unchecked("no verdict".to_string()),
                ..template_inputs(&passing)
            },
            &names(),
        ),
    ));
    rows.push((
        "not-conserved",
        row(
            TemplateInputs {
                verdict: VerdictInput::Classes(vec!["not-conserved(call)".to_string()]),
                ..template_inputs(&passing)
            },
            &names(),
        ),
    ));
    let opaque_read =
        template_record(template_candidate(extract_field_template_module(), Vec::new()));
    rows.push(("invalid", row(template_inputs(&opaque_read), &names())));
    rows.push(("extraction-not-conserved", dropped_call_extraction()));
    for (class, refusal) in &rows {
        assert_eq!(refusal.class(), *class, "{refusal:?}");
        let reason = refusal.reason();
        assert!(reason.starts_with(class), "the recorded reason names its class: {reason}");
    }
    assert_eq!(
        rows[5].1.reason(),
        "not-conserved(call)",
        "a D28 refusal records the verdict's own class labels"
    );
    assert_eq!(rows[6].1.reason(), "unsited-panic(overflow)");
    // The control: the same body, conserved and named, encodes.
    assert!(build_entry_module(&conserved(&base), &names()).is_ok());
}

#[test]
fn an_assert_without_a_panic_site_is_not_encoded() {
    // A reachable check refuses; the same check in an unreachable block does not count.
    let mut module = per_body_module(vec![ret(0)]);
    let mut dead = Block::new(BlockId::new(1));
    dead.body = vec![
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::InBounds),
        node(Inst::Unreachable),
    ];
    module.functions[0].blocks.push(dead);
    assert!(unsited_checks(&module.functions[0]).is_empty(), "an unreachable check is not code");

    let live = per_body_module(vec![
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::InBounds),
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::DivNonZero),
        node(Inst::Assert { cond: v(0), kind: trust_ir::AssertKind::Unspecified, site: None }),
        ret(0),
    ]);
    assert_eq!(unsited_checks(&live.functions[0]), vec!["bounds", "div-zero", "other"]);
    let c = candidate(live, Vec::new());
    assert_eq!(
        build_entry_module(&conserved(&c), &names()),
        Err(EntryRefusal::UnsitedPanic(vec!["bounds", "div-zero", "other"]))
    );
}

#[test]
fn extraction_that_adds_or_drops_an_effect_is_refused() {
    let c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let entry = assemble_entry(&c, &names()).expect("encodes");
    assert_eq!(check_extraction(&c.module, &entry), Ok(()), "an honest extraction passes");
    let mut dropped = entry.clone();
    dropped.functions[0].blocks[0].body = vec![ret(0)];
    assert!(matches!(
        check_extraction(&c.module, &dropped),
        Err(EntryRefusal::ExtractionNotConserved(_))
    ));
    let mut added = entry.clone();
    added.functions[0].blocks[0]
        .body
        .insert(0, node_r(Inst::Call { callee: FuncId::new(1), args: vec![v(0)] }, 9));
    assert!(matches!(
        check_extraction(&c.module, &added),
        Err(EntryRefusal::ExtractionNotConserved(_))
    ));
}

/// The entry is a pure function of the judged body: two INDEPENDENTLY built candidates of the same
/// body (one as the lowering hands it over, one through the registry's binary form, each with its
/// own fixture names) frame to the same bytes. This is the in-process half only; that two
/// COMPILATIONS write the same entries, from different build directories, with and without
/// `--remap-path-prefix`, is pinned by `tests/run-make/trust-ir-rmeta-entry-roundtrip` (review
/// 2026-10-05: this test was named as if it covered two builds, and the fixture's two builds
/// shared one source path, so neither could see a path in an entry).
#[test]
fn the_entry_is_a_pure_function_of_the_judged_body() {
    let c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let binding = EntryBinding { stable_crate_id: 0x1234, local_hash: 0x5678 };
    let evidence = encode_evidence(&sample_evidence());
    let a = frame_entry(&assemble_entry(&c, &names()).unwrap(), binding, true, &evidence)
        .expect("frame_entry: test fixture");
    let rebuilt = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let stored = StoredCandidate {
        module: Some(
            trust_ir::binary::serialize_module(&rebuilt.module)
                .expect("serialize_module: test fixture"),
        ),
        callees: rebuilt.callees,
        global_origins: rebuilt.global_origins,
        body_kind: rebuilt.body_kind,
        not_lowered: rebuilt.not_lowered,
    };
    let loaded = stored.load().expect("loads");
    let b = frame_entry(&assemble_entry(&loaded, &names()).unwrap(), binding, true, &evidence)
        .expect("frame_entry: test fixture");
    assert_eq!(a, b, "the entry is a pure function of the judged body");
    let decoded = decode_entry(&a).expect("decodes");
    assert_eq!(decoded.binding, binding);
    assert_eq!(decoded.producer_trust_ir_version, trust_ir::binary::VERSION);
    assert_eq!(decoded.module, assemble_entry(&c, &names()).unwrap());
    assert_eq!(decoded.digest, decoded.module.stable_digest().bytes);
    assert_eq!(decode_evidence(&decoded.evidence), Ok(sample_evidence()));
}

#[test]
fn a_tampered_entry_is_refused_by_its_digest_magic_schema_or_version() {
    let c = candidate(per_body_module(mix_body()), Vec::new());
    let binding = EntryBinding { stable_crate_id: 1, local_hash: 2 };
    let good = frame_entry(&assemble_entry(&c, &names()).unwrap(), binding, true, &[])
        .expect("frame_entry: test fixture");
    assert!(decode_entry(&good).is_ok());
    // One flipped byte inside the recorded digest.
    let mut bad = good.clone();
    bad[8 + 4 + 4 + 16] ^= 1;
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::EnvelopeDigest);
    let mut bad = good.clone();
    bad[0] ^= 1;
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Magic);
    let mut bad = good.clone();
    bad[8] = 99;
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Schema(99));
    bad[8..12].copy_from_slice(&2u32.to_le_bytes());
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Schema(2));
    bad[8..12].copy_from_slice(&3u32.to_le_bytes());
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Schema(3));
    bad[8..12].copy_from_slice(&4u32.to_le_bytes());
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Schema(4));
    bad[8..12].copy_from_slice(&5u32.to_le_bytes());
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Schema(5));
    let mut bad = good.clone();
    bad[12..16].copy_from_slice(&(trust_ir::binary::VERSION + 1).to_le_bytes());
    assert!(matches!(decode_entry(&bad), Err(EntryDecodeError::TrustIrVersion { .. })));
    assert!(matches!(decode_entry(&good[..good.len() - 1]), Err(EntryDecodeError::Truncated(_))));
    let mut long = good.clone();
    long.push(0);
    assert_eq!(decode_entry(&long).unwrap_err(), EntryDecodeError::TrailingBytes(1));
}

fn sample_evidence() -> Evidence {
    Evidence {
        effects: vec![
            (
                EvidenceEffectKind::Call(EvidenceCall {
                    ids: vec![(1, 2), (3, 4)],
                    site: Some("00ab".to_string()),
                    equivalence: Some(7),
                    enum_result: true,
                    enum_args: vec![false, true],
                }),
                0,
            ),
            (EvidenceEffectKind::IndirectCall, 1),
            (EvidenceEffectKind::Store(u32::MAX - 1), 2),
            (EvidenceEffectKind::Drop { destructor: true }, 3),
            (EvidenceEffectKind::Assert(2), 0),
            (EvidenceEffectKind::Asm { empty_noreturn: false }, 1),
            (EvidenceEffectKind::Yield, 2),
        ],
        arg_count: 2,
        arg_enum: vec![true, false],
        ret_enum: true,
        store_values: vec![(0, 1), (u32::MAX, 2)],
        exact_store_args: vec![],
        enum_types: vec![u128::MAX, 5],
        drop_oracle: Some(vec![EvidenceOracleDrop {
            block: 3,
            identity: (1, 17),
            ty: 99,
            span: 3,
            style: Some(1),
            projected: false,
            destructor: true,
        }]),
        drop_dead_blocks: vec![4, 6],
        drop_claim: Some((
            vec![EvidenceDropKey { identity: (0, 1), ty: 99, span: 3, style: 0 }],
            1,
            vec![true],
        )),
        ledger: vec![EvidenceLedgerRow { func_id: 1, ids: vec![(1, 2)], site: None }],
        collapsed_enum_types: vec![5],
        degraded_structs: vec![0, 3],
        union_lane: true,
        enum_param_lane: false,
    }
}

#[test]
fn evidence_round_trips_and_refuses_what_it_does_not_know() {
    use crate::effect_conservation::Equivalence;

    let e = sample_evidence();
    let bytes = encode_evidence(&e);
    assert_eq!(decode_evidence(&bytes), Ok(e.clone()));
    assert_eq!(decode_evidence(&encode_evidence(&Evidence::default())), Ok(Evidence::default()));
    // Every strict prefix is refused (a length or a field runs off the end), never decoded.
    for cut in 0..bytes.len() {
        assert!(decode_evidence(&bytes[..cut]).is_err(), "a {cut}-byte prefix decoded");
    }
    // Any other schema is refused by number (the field is the u32 after the 8-byte magic).
    let mut bad = bytes.clone();
    bad[8..12].copy_from_slice(&(EVIDENCE_SCHEMA + 1).to_le_bytes());
    assert_eq!(decode_evidence(&bad), Err(EntryDecodeError::EvidenceSchema(EVIDENCE_SCHEMA + 1)));
    bad[8..12].copy_from_slice(&2u32.to_le_bytes());
    assert_eq!(decode_evidence(&bad), Err(EntryDecodeError::EvidenceSchema(2)));

    // Keep the existing wire meanings fixed, and exercise the new equivalence
    // through the same evidence encoder/decoder a metadata consumer reads.
    for (equivalence, code) in [
        (Equivalence::PureIntrinsic, 0),
        (Equivalence::SliceLen, 1),
        (Equivalence::RangeIntoIter, 2),
        (Equivalence::RangeNext, 3),
        (Equivalence::OptionDiscriminant, 4),
        (Equivalence::TryBranch, 5),
        (Equivalence::TryResidual, 6),
        (Equivalence::BuiltinEq, 7),
        (Equivalence::FormatArguments, 8),
        (Equivalence::BoolFromInteger, 9),
    ] {
        assert_eq!(equivalence_code(equivalence), code);
        let mut evidence = sample_evidence();
        let EvidenceEffectKind::Call(call) = &mut evidence.effects[0].0 else {
            panic!("the fixture starts with a call");
        };
        call.equivalence = Some(code);
        assert_eq!(decode_evidence(&encode_evidence(&evidence)), Ok(evidence));
    }
    let mut unknown = sample_evidence();
    let EvidenceEffectKind::Call(call) = &mut unknown.effects[0].0 else {
        panic!("the fixture starts with a call");
    };
    call.equivalence = Some(10);
    assert!(decode_evidence(&encode_evidence(&unknown)).is_err());
}

/// Fixture spelling: a `DefId` is `(0xC0DE, index)`; a site is `index:` plus its arg count.
struct Spell;

impl EvidenceSpelling for Spell {
    fn def(&self, def: DefId) -> StableDef {
        (0xC0DE, def.index.as_u32() as u64)
    }
    fn site(&self, def: DefId, args: &[crate::SiteArg]) -> String {
        format!("{}:{}", def.index.as_u32(), args.len())
    }
}

#[test]
fn evidence_spells_defs_by_stable_hash_and_spans_by_body_local_ordinal() {
    let span_a = DUMMY_SP;
    let span_b = DUMMY_SP.with_lo(rustc_span::BytePos(5));
    let census = MirCensus {
        effects: vec![
            MirEffect {
                kind: MirEffectKind::Call {
                    ids: vec![def(9)],
                    site_args: Some(Vec::new()),
                    equivalence: None,
                    enum_result: false,
                    enum_args: vec![false],
                },
                span: span_b,
            },
            MirEffect { kind: MirEffectKind::Store(MemRoot::Arg(1)), span: span_a },
            MirEffect { kind: MirEffectKind::Drop { destructor: false }, span: span_b },
        ],
        arg_count: 2,
        ..MirCensus::default()
    };
    let retained = RetainedEvidence {
        census,
        drop_claim: None,
        collapsed_enum_types: vec![7],
        degraded_structs: vec![2],
        union_lane: false,
        enum_param_lane: true,
    };
    let e = evidence_of(&retained, &[callee(1, 9)], &Spell);
    assert_eq!(
        e.effects,
        vec![
            (
                EvidenceEffectKind::Call(EvidenceCall {
                    ids: vec![(0xC0DE, 9)],
                    site: Some("9:0".to_string()),
                    equivalence: None,
                    enum_result: false,
                    enum_args: vec![false],
                }),
                0
            ),
            (EvidenceEffectKind::Store(1), 1),
            (EvidenceEffectKind::Drop { destructor: false }, 0),
        ],
        "the same span is the same ordinal; ordinals count from first appearance"
    );
    assert_eq!(
        e.ledger,
        vec![EvidenceLedgerRow {
            func_id: 1,
            ids: vec![(0xC0DE, 9)],
            site: Some("9:0".to_string())
        }],
        "a ledger row whose site and resolved identity agree carries one id"
    );
    assert_eq!(
        (e.collapsed_enum_types, e.degraded_structs, e.union_lane, e.enum_param_lane),
        (vec![7], vec![2], false, true),
        "the session-wide and producer inputs of the judgement travel with the census"
    );
}

/// A candidate waits for metadata in trust-ir's binary form; it loads back as the module the
/// lowering produced, and a module that does not decode is refused by name, never encoded.
#[test]
fn a_stored_candidate_loads_back_the_lowered_module() {
    let c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let stored = StoredCandidate {
        module: Some(
            trust_ir::binary::serialize_module(&c.module).expect("serialize_module: test fixture"),
        ),
        callees: c.callees.clone(),
        global_origins: c.global_origins.clone(),
        body_kind: c.body_kind,
        not_lowered: c.not_lowered.clone(),
    };
    let loaded = stored.load().expect("loads");
    assert_eq!(loaded.module, c.module);
    assert_eq!(assemble_entry(&loaded, &names()), assemble_entry(&c, &names()));
    let broken = StoredCandidate { module: Some(b"not a module".to_vec()), ..stored };
    assert!(matches!(broken.load(), Err(EntryRefusal::Invalid(_))));
}

/// Review 2026-10-05 (must-fix): a `#[track_caller]` callee's symbol takes a hidden
/// `&'static Location` argument, so a declaration signed `(u32) -> (u32)` under that symbol, and a
/// call passing one argument, is a call with the wrong arity once linked. Measured before this
/// refusal: `x.unwrap()` and a call to a `#[track_caller]` `tc` were ENCODED, declaring
/// `Option::<u32>::unwrap` and `tc` as `(..) -> (..)` with no location; a `#[track_caller]` body
/// was encoded under its own symbol with the wrong arity.
#[test]
fn a_track_caller_body_or_callee_is_refused_never_declared_with_the_wrong_arity() {
    let c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    let callee_tc = Names { track_caller: [1].into_iter().collect(), ..names() };
    let refusal = build_entry_module(&conserved(&c), &callee_tc).expect_err("refused");
    assert_eq!(refusal.class(), "caller-location");
    assert!(refusal.reason().contains("callee FuncId(1) `dep::callee9`"), "{}", refusal.reason());
    let body_tc = Names { body_track_caller: true, ..names() };
    let refusal = build_entry_module(&conserved(&c), &body_tc).expect_err("refused");
    assert_eq!(refusal.class(), "caller-location");
    assert!(refusal.reason().contains("the body is #[track_caller]"), "{}", refusal.reason());
    // A body with no callee at all is refused for its own attribute too.
    let leaf = candidate(per_body_module(mix_body()), Vec::new());
    assert!(matches!(
        build_entry_module(&conserved(&leaf), &body_tc),
        Err(EntryRefusal::CallerLocation(_))
    ));
    // The control: the same bodies, no attribute, encode.
    assert!(build_entry_module(&conserved(&c), &names()).is_ok());
    assert!(build_entry_module(&conserved(&leaf), &names()).is_ok());
}

/// Review 2026-10-05 (must-fix): an entry is written into rmeta, so its source-file table must be
/// spelled as rustc's metadata spells the files (after `--remap-path-prefix`), not as the producer
/// interned them (the local path). Measured before: a build with
/// `--remap-path-prefix=$PWD=/REMAPPED` wrote the unremapped absolute path into every entry.
#[test]
fn source_files_are_spelled_as_metadata_spells_them_never_by_their_local_path() {
    let mut module = per_body_module(mix_body());
    module.files = vec![LOCAL_FILE.to_string()];
    let c = candidate(module, Vec::new());
    let entry = build_entry_module(&conserved(&c), &names()).expect("encodes");
    assert_eq!(entry.files, vec![REMAPPED_FILE.to_string()]);
    let bytes = frame_entry(&entry, EntryBinding { stable_crate_id: 1, local_hash: 2 }, true, &[])
        .expect("frame_entry: test fixture");
    let contains = |needle: &str| bytes.windows(needle.len()).any(|w| w == needle.as_bytes());
    assert!(contains(REMAPPED_FILE));
    assert!(!contains("/build/dep"), "the local path never reaches the entry bytes");
    // A file the source map does not name is refused, and the recorded reason (which rmeta
    // carries) does not repeat the path.
    let mut module = per_body_module(mix_body());
    module.files = vec!["/build/elsewhere/secret.rs".to_string()];
    let refusal = build_entry_module(&conserved(&candidate(module, Vec::new())), &names())
        .expect_err("refused");
    assert_eq!(refusal.class(), "invalid");
    assert!(!refusal.reason().contains("secret"), "{}", refusal.reason());
}

/// Review 2026-10-05 (should-fix): the evidence must carry every input of the judgement. The one
/// `ir_census` input it does not carry, the callee result types, is in the entry's declarations:
/// the census of the ENTRY with no result-type map equals the census of the per-body module with
/// the producer's map, including a placeholder (`bool`) result.
#[test]
fn the_census_of_the_entry_equals_the_producers_census_of_the_body() {
    use crate::effect_conservation::{LedgerRow, LedgeredLanes, ir_census};
    let body = vec![node_r(Inst::Call { callee: FuncId::new(1), args: vec![v(0)] }, 1), ret(0)];
    let mut bool_callee = callee(1, 9);
    bool_callee.ret_ty = Some(Ty::Bool);
    let c = candidate(per_body_module(body), vec![bool_callee]);
    let entry = build_entry_module(&conserved(&c), &names()).expect("encodes");
    let ledger: BTreeMap<FuncId, LedgerRow> =
        [(FuncId::new(1), LedgerRow::ids(vec![def(9)]))].into_iter().collect();
    let producer_returns: BTreeMap<FuncId, Ty> = [(FuncId::new(1), Ty::Bool)].into_iter().collect();
    let lanes = LedgeredLanes::default();
    let producer = ir_census(
        &c.module,
        &c.module.functions[0],
        &ledger,
        &producer_returns,
        &BTreeSet::new(),
        lanes,
    );
    let consumer = ir_census(
        &entry,
        &entry.functions[0],
        &ledger,
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    );
    assert_eq!(format!("{producer:?}"), format!("{consumer:?}"));
    assert!(
        format!("{consumer:?}").contains("placeholder_result: true"),
        "the bool result reads as a placeholder through the declaration: {consumer:?}"
    );
}

/// A `Lowered` in the posture an encodable body has: one function, no tag, every flag clear.
fn clean_lowered() -> Lowered {
    Lowered {
        module: per_body_module(mix_body()),
        global_origins: Vec::new(),
        body_kind: BodyKind::Fn,
        opaque_collapse: false,
        enum_declines: Vec::new(),
        union_lane: false,
        layout_withheld_structs: Vec::new(),
        enum_param_lane: false,
        symbolic: false,
        unsubstituted_opaque_return: false,
        unsupported: Vec::new(),
        contains_call: false,
        place_path_carrier: false,
        zst_closure_arg: false,
        coroutine_frame_ptr: false,
        fnptr_adapter: false,
        thin_reborrows: Vec::new(),
        mut_reborrows: Vec::new(),
        callees: Vec::new(),
        pending_consts: Vec::new(),
        enum_fold_switch_blocks: std::collections::HashSet::new(),
    }
}

/// Review 2026-10-05 (should-fix): `not_lowered_reasons` is the only guard that keeps a body
/// holding a placeholder (a pending-const sentinel, an opaque collapse, a placeholder lane) out of
/// rmeta, and D28 does not back it up (it checks effects, not values). Each flag alone must be
/// exactly its own reason, so deleting any one from the list turns this red; the flags that are
/// not reasons must stay silent, so a body is not refused for them.
#[test]
fn every_not_lowered_flag_is_its_own_reason_and_nothing_else_is_one() {
    let reasons = |f: &dyn Fn(&mut Lowered)| {
        let mut l = clean_lowered();
        f(&mut l);
        not_lowered_reasons(&l)
    };
    assert_eq!(reasons(&|_| {}), Vec::<String>::new(), "a clean lowering has no reason");
    let one = |f: &dyn Fn(&mut Lowered), expected: &str| {
        assert_eq!(reasons(f), vec![expected.to_string()], "the reason for `{expected}`");
    };
    one(&|l| l.symbolic = true, "symbolic");
    one(&|l| l.unsubstituted_opaque_return = true, "unsubstituted opaque return");
    one(
        &|l| {
            l.pending_consts.push(crate::PendingConst {
                value: v(1),
                def_id: def(7),
                span: DUMMY_SP,
                is_bool: false,
                is_float: false,
                signed: false,
                bits: 32,
                composite: false,
                pointer_width: false,
                site_args: None,
                str_global: None,
                static_global: None,
                promoted_global: None,
            })
        },
        "pending-const sentinel",
    );
    one(&|l| l.opaque_collapse = true, "opaque collapse");
    one(&|l| l.union_lane = true, "union lane");
    one(&|l| l.enum_param_lane = true, "enum-parameter lane");
    one(&|l| l.fnptr_adapter = true, "fn-pointer adapter");
    one(&|l| l.coroutine_frame_ptr = true, "coroutine frame pointer");
    one(&|l| l.zst_closure_arg = true, "ZST callable stand-in");
    one(&|l| l.place_path_carrier = true, "place-path value carrier");
    one(&|l| l.layout_withheld_structs.push(trust_ir::StructId::new(0)), "layout withheld");
    one(
        &|l| {
            let extra = l.module.functions[0].clone();
            l.module.functions.push(extra);
        },
        "2 functions in the per-body module",
    );
    one(
        &|l| {
            l.module.functions.clear();
        },
        "0 functions in the per-body module",
    );
    // The producer's own tags, sorted and deduplicated.
    assert_eq!(
        reasons(&|l| {
            l.unsupported = vec![
                ("a".to_string(), "Ty(float-width)"),
                ("b".to_string(), "Call(unsupported arg)"),
                ("c".to_string(), "Ty(float-width)"),
            ]
        }),
        vec!["Call(unsupported arg)".to_string(), "Ty(float-width)".to_string()]
    );
    // Not reasons: a body with calls, globals, reborrows or a census of enum declines is
    // encodable (each is named or refused elsewhere, or is flip-only evidence).
    let silent: [&dyn Fn(&mut Lowered); 6] = [
        &|l| l.contains_call = true,
        &|l| l.global_origins.push(GlobalOrigin::BodyLocal),
        &|l| l.enum_declines.push(("dep::E".to_string(), "why".to_string())),
        &|l| {
            l.thin_reborrows.push(crate::ThinReborrow {
                value: v(0),
                provenance: crate::ThinReborrowProvenance::CallResult,
            })
        },
        &|l| l.callees.push(callee(1, 9)),
        &|l| {
            l.enum_fold_switch_blocks.insert(BlockId::new(0));
        },
    ];
    for f in silent {
        assert_eq!(reasons(f), Vec::<String>::new());
    }
    // Several at once: tags first, then the flags in their fixed order.
    assert_eq!(
        reasons(&|l| {
            l.place_path_carrier = true;
            l.symbolic = true;
            l.unsupported = vec![("a".to_string(), "Ty(float-width)")];
        }),
        vec![
            "Ty(float-width)".to_string(),
            "symbolic".to_string(),
            "place-path value carrier".to_string()
        ]
    );
}

/// Review 2026-10-05 (should-fix): the re-derivation guard decides every callee name an entry
/// carries ("RE-DERIVED, NOT TRUSTED"), and no test reached it: the fixture names above never call
/// rustc, and the roundtrip fixture's only edges are plain local calls. Its decision is pure; each
/// branch is pinned here, and the rustc half end to end by
/// `tests/run-make/trust-ir-rmeta-entry-rederivation` (an intrinsic, a drop-glue shim, a self
/// edge).
#[test]
fn the_rederivation_guard_names_only_the_ledgers_own_item_at_its_own_key() {
    let ledger = callee(1, 9).concrete_key.unwrap();
    let shown = "dep::callee9";
    let facts = || RederivedCallee {
        resolved: &shown,
        is_ledger_item: true,
        key: Some(ledger.clone()),
        is_self: false,
        requires_caller_location: false,
    };
    assert_eq!(judge_rederived_callee(&ledger, &facts()), Ok(()), "the plain item at its key");
    let unnamed = |r: RederivedCallee<'_>| match judge_rederived_callee(&ledger, &r) {
        Err(CalleeNameRefusal::Unnamed(why)) => why,
        other => panic!("expected an unnamed edge, got {other:?}"),
    };
    // An intrinsic, a virtual call, a shim or another item: no symbol of its own.
    let why = unnamed(RederivedCallee { is_ledger_item: false, key: None, ..facts() });
    assert!(why.contains("`dep::callee9`, which is not the plain item the ledger linked"), "{why}");
    // The ledger's item, but at another instance than the ledger keyed.
    let other = ConcreteCalleeKey::test_only(
        DefinitionIdentity::test_only(0xC0DE, 9),
        ConcreteInstanceKind::Item,
        vec![crate::lineage::ConcreteInstanceArg::Ty(crate::lineage::ConcreteInstanceTy::Bool)],
    );
    assert_ne!(other, ledger);
    let why = unnamed(RederivedCallee { key: Some(other), ..facts() });
    assert!(why.contains("which is not the instance the ledger keyed"), "{why}");
    let why = unnamed(RederivedCallee { key: None, ..facts() });
    assert!(why.contains("args are not encodable"), "{why}");
    let why = unnamed(RederivedCallee { is_self: true, ..facts() });
    assert!(why.contains("a self edge"), "{why}");
    assert_eq!(
        judge_rederived_callee(
            &ledger,
            &RederivedCallee { requires_caller_location: true, ..facts() }
        ),
        Err(CalleeNameRefusal::CallerLocation)
    );
    // The order is the diagnosis: a resolution that is not the item is refused as such even when
    // every later fact would refuse too.
    let why = unnamed(RederivedCallee {
        is_ledger_item: false,
        key: None,
        is_self: true,
        requires_caller_location: true,
        ..facts()
    });
    assert!(why.contains("not the plain item"), "{why}");
}

// =============================================================================================
// Step 6.5.1: the template builder
// =============================================================================================

use crate::template_lowering::{LaneFacts, LaneParam, TemplateLane, type_param_sentinel};

fn t0() -> Ty {
    type_param_sentinel(0)
}

/// A one-function SENTINEL module (a template lowering's per-body module): `fn(T, i32) -> i32`
/// whose entry block binds `v0: T`, `v1: i32` and runs `body`.
fn sentinel_module(body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("dep");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![t0(), Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "dep::pick", ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0)).with_param(v(0), t0()).with_param(v(1), Ty::I32);
    b.body = body;
    f.blocks = vec![b];
    module.functions.push(f);
    module
}

/// `pick<T>(_: T, x: i32) -> i32 { callee1(x) }`: one ground callee.
fn calling_template_module() -> Module {
    sentinel_module(vec![
        node_r(Inst::Call { callee: FuncId::new(1), args: vec![v(1)] }, 2),
        node(Inst::Return { values: vec![v(2)] }),
    ])
}

/// A body whose UNREACHABLE block carries a proof-annotated check: no reachable check (so no
/// `unsited-panic`), but a proof surface T7 refuses (`TemplateUnsupported`).
fn proof_surface_template_module() -> Module {
    let mut module = sentinel_module(vec![node(Inst::Return { values: vec![v(1)] })]);
    let mut dead = Block::new(BlockId::new(1));
    dead.body = vec![
        node_r(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) }, 3),
        node(Inst::Assert { cond: v(3), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::NoOverflow),
        node(Inst::Return { values: vec![v(1)] }),
    ];
    module.functions[0].blocks.push(dead);
    module
}

/// A body that reads a field of a value of the parameter type: no amendment-S structural rule
/// names it (T4 lists no `ExtractField`), and its skolem instance does not validate (T6).
fn extract_field_template_module() -> Module {
    sentinel_module(vec![
        node_r(Inst::ExtractField { ty: t0(), aggregate: v(0), field: 0 }, 2),
        node(Inst::Return { values: vec![v(1)] }),
    ])
}

fn template_candidate(module: Module, callees: Vec<CalleeRef>) -> TemplateCandidate {
    let global_origins = vec![GlobalOrigin::BodyLocal; module.globals.len()];
    TemplateCandidate {
        module,
        callees,
        global_origins,
        facts: LaneFacts { params: vec![LaneParam::Type], ..LaneFacts::default() },
    }
}

fn template_record(c: TemplateCandidate) -> TemplateRecord {
    TemplateRecord { body_kind: BodyKind::Fn, capture: Ok(c) }
}

fn refused_template(refusal: CaptureRefusal) -> TemplateRecord {
    TemplateRecord { body_kind: BodyKind::Fn, capture: Err(refusal) }
}

/// The inputs every gate passes: recorded once, the lane on, not Clean-origin, CONSERVED.
fn template_inputs(record: &TemplateRecord) -> TemplateInputs<'_> {
    TemplateInputs {
        record: Some(record),
        duplicated: false,
        capture_on: true,
        clean_origin: false,
        verdict: VerdictInput::Classes(Vec::new()),
        identity: "dep::pick".to_string(),
    }
}

/// Test 11's second half: the judged module calls `callee1`, the template built from a module
/// that lost the call between judgement and build does not.
fn dropped_call_extraction() -> EntryRefusal {
    let judged = template_candidate(calling_template_module(), vec![callee(1, 9)]);
    let lost = template_candidate(
        sentinel_module(vec![node(Inst::Return { values: vec![v(1)] })]),
        vec![],
    );
    let (template, _) = assemble_template(&lost, &names(), "dep::pick".to_string())
        .expect("the module without the call assembles");
    check_template_extraction(&judged, &template).expect_err("a lost call is refused")
}

/// Test 9 (INC6.5-SITES): a reachable unsited check refuses the template BEFORE any template is
/// constructed — at capture time the record stores no module, and the builder refuses it ahead
/// of the body's caller-location gate and of assembly (where an unnamed callee would refuse).
#[test]
fn unsited_panic_precedes_template_construction() {
    let checking = sentinel_module(vec![
        node(Inst::Assert { cond: v(1), kind: trust_ir::AssertKind::Unspecified, site: None })
            .with_proof(ProofAnnotation::NoOverflow),
        node(Inst::Return { values: vec![v(1)] }),
    ]);
    let lowered = Lowered { module: checking.clone(), ..clean_lowered() };
    let lane = TemplateLane::new(
        rustc_middle::ty::TypingEnv::fully_monomorphized(),
        vec![(0, LaneParam::Type)],
    );
    let stored = StoredTemplate::of_lowering(&lowered, &lane);
    assert_eq!(stored.module_bytes(), None, "a refused capture stores no module");
    let record = stored.load().expect("loads");
    assert!(
        matches!(record.capture, Err(CaptureRefusal::UnsitedPanic(ref k)) if k == &["overflow"])
    );
    let every_later_gate_refuses =
        Names { unnamed: [1].into_iter().collect(), body_track_caller: true, ..names() };
    assert_eq!(
        template_row(&template_inputs(&record), &every_later_gate_refuses).reason(),
        "unsited-panic(overflow)"
    );
    // The builder's own gate 7, on a stored module that carries a reachable check.
    let hand_built = template_record(template_candidate(checking, vec![callee(1, 9)]));
    assert_eq!(
        build_template(&template_inputs(&hand_built), &every_later_gate_refuses)
            .expect_err("refused")
            .reason(),
        "unsited-panic(overflow)"
    );
    // The control: the same check in an unreachable block does not count.
    let passing =
        template_record(template_candidate(calling_template_module(), vec![callee(1, 9)]));
    assert!(build_template(&template_inputs(&passing), &names()).is_ok());
}

fn body_verdict(
    tags: Vec<crate::effect_conservation::Tag>,
) -> crate::effect_conservation::BodyVerdict {
    crate::effect_conservation::BodyVerdict {
        def_path: "dep::pick".to_string(),
        clean: true,
        tags,
        assembled: None,
        equivalences: BTreeMap::new(),
        drop_claim_live: None,
        drop_sites: Vec::new(),
    }
}

/// Test 10 (INC6.5-JUDGE): a template is judged by ITS OWN verdict. The mainline verdict of the
/// same definition — conserved or not — is never read: a conserved mainline body with a refused
/// template refuses the template, a refused mainline body with a conserved template does not,
/// and a template with no verdict of its own is unchecked whatever the mainline says.
#[test]
fn a_template_is_judged_by_its_own_verdict_never_the_mainline_one() {
    use crate::effect_conservation::{ConservationVerdicts, Effect, Tag, TagKind};
    let refused =
        || vec![Tag { kind: TagKind::NotConserved(Effect::Call), site: "a call".to_string() }];
    let passing =
        template_record(template_candidate(calling_template_module(), vec![callee(1, 9)]));
    let row = |v: &ConservationVerdicts| {
        let inputs =
            TemplateInputs { verdict: template_verdict_input(v, 7), ..template_inputs(&passing) };
        template_row(&inputs, &names())
    };
    let mainline_conserved_template_refused = ConservationVerdicts::finalized_for_test(
        [(7, body_verdict(Vec::new()))].into_iter().collect(),
        [(7, body_verdict(refused()))].into_iter().collect(),
    );
    assert_eq!(row(&mainline_conserved_template_refused).reason(), "not-conserved(call)");
    let mainline_refused_template_conserved = ConservationVerdicts::finalized_for_test(
        [(7, body_verdict(refused()))].into_iter().collect(),
        [(7, body_verdict(Vec::new()))].into_iter().collect(),
    );
    assert_eq!(
        row(&mainline_refused_template_conserved),
        EntryRefusal::TemplatePending(TEMPLATE_VALIDATED.to_string())
    );
    let mainline_only = ConservationVerdicts::finalized_for_test(
        [(7, body_verdict(Vec::new()))].into_iter().collect(),
        BTreeMap::new(),
    );
    assert_eq!(row(&mainline_only).class(), "conservation-unchecked");
    assert_eq!(row(&ConservationVerdicts::default()).class(), "conservation-unchecked");
}

/// Test 11: the effect census of the template's SKOLEM instance equals the census the template
/// was judged with (and so does the shape) — measured on a body with a parameter-typed value, a
/// ground callee declared by symbol and a placeholder (`bool`) call result.
#[test]
fn the_skolem_census_of_the_template_equals_the_judged_census() {
    use crate::effect_conservation::{census_ledger, ir_census};
    let mut bool_callee = callee(1, 9);
    bool_callee.ret_ty = Some(Ty::Bool);
    bool_callee.params = crate::ParamSignature::Signed(vec![Ty::I32]);
    let module = sentinel_module(vec![
        node_r(Inst::Call { callee: FuncId::new(1), args: vec![v(1)] }, 2),
        node(Inst::Return { values: vec![v(1)] }),
    ]);
    let c = template_candidate(module, vec![bool_callee]);
    let (t, _) = assemble_template(&c, &names(), "dep::pick".to_string()).expect("assembles");
    assert_eq!(trust_ir_build::template::validate_template(&t), Vec::new());
    let (ledger, returns) = census_ledger(&c.callees);
    let lanes = crate::effect_conservation::LedgeredLanes::default();
    let judged =
        ir_census(&c.module, &c.module.functions[0], &ledger, &returns, &BTreeSet::new(), lanes);
    let skolem = trust_ir_build::template::skolem_instance(&t).expect("a skolem instance");
    let skolem_census =
        ir_census(&skolem, &skolem.functions[0], &ledger, &returns, &BTreeSet::new(), lanes);
    assert_eq!(skolem_census, judged, "measured: the skolem census is the judged census");
    assert!(format!("{judged:?}").contains("placeholder_result: true"), "{judged:?}");
    assert_eq!(check_template_extraction(&c, &t), Ok(()));
}

/// Test 11, second half: a template whose skolem census differs from the judged one (a call
/// dropped between judgement and build) is `extraction-not-conserved`.
#[test]
fn a_template_whose_skolem_census_differs_is_extraction_not_conserved() {
    let refusal = dropped_call_extraction();
    assert_eq!(refusal.class(), "extraction-not-conserved");
    assert!(refusal.reason().starts_with("extraction-not-conserved(template: "), "{refusal:?}");
}

/// Test 12: no template passes before `validate_template` accepts it — a field read of a
/// parameter-typed value is named by no structural rule, and its skolem instance (a fieldless
/// struct) is refused by the level-R validator: `invalid(T6 ..)`.
#[test]
fn a_template_is_never_accepted_before_validate_template_accepts_it() {
    let record = template_record(template_candidate(extract_field_template_module(), Vec::new()));
    let refusal = build_template(&template_inputs(&record), &names()).expect_err("refused");
    assert_eq!(refusal.class(), "invalid");
    assert!(refusal.reason().starts_with("invalid(T6"), "{refusal:?}");
}

/// Test 13 (INC6.5-JUDGE): the evidence of a definition with a template record keeps the
/// template's producer half and the set its template was JUDGED with (`collapsed_t`); every other
/// definition keeps the mainline set. Fails if `retain_evidence` passes `collapsed` for both.
#[test]
fn the_template_evidence_carries_the_set_it_was_judged_with() {
    use crate::effect_conservation::{LedgeredLanes, ProducerBody, producer_body};
    const MAINLINE_ENUM: u128 = 0xA;
    const TEMPLATE_ENUM: u128 = 0xB;
    let census = || MirCensus {
        enum_types: [MAINLINE_ENUM, TEMPLATE_ENUM].into_iter().collect(),
        ..MirCensus::default()
    };
    let body = |collapsed: &[u128], claim_emitted: usize| -> ProducerBody {
        producer_body(
            "dep::x".to_string(),
            &per_body_module(mix_body()),
            &[],
            BodyKind::Fn,
            true,
            &[],
            LedgeredLanes::default(),
            collapsed.iter().copied().collect(),
            Some(crate::drops::DropClaim { emitted: claim_emitted, ..Default::default() }),
            None,
        )
    };
    let mut mir: BTreeMap<u32, MirCensus> = [(1, census()), (2, census())].into_iter().collect();
    let mut producer: BTreeMap<u32, ProducerBody> =
        [(1, body(&[MAINLINE_ENUM], 0)), (2, body(&[MAINLINE_ENUM], 0))].into_iter().collect();
    let mut template: BTreeMap<u32, ProducerBody> =
        [(1, body(&[TEMPLATE_ENUM], 3))].into_iter().collect();
    let collapsed: BTreeSet<u128> = [MAINLINE_ENUM].into_iter().collect();
    let collapsed_t: BTreeSet<u128> = [MAINLINE_ENUM, TEMPLATE_ENUM].into_iter().collect();
    let retained =
        retained_evidence(&mut mir, &mut producer, &mut template, &collapsed, &collapsed_t);
    assert_eq!(
        retained[&1].collapsed_enum_types,
        vec![MAINLINE_ENUM, TEMPLATE_ENUM],
        "the template's collapse, which the mainline set does not hold, is retained"
    );
    assert_eq!(
        retained[&1].drop_claim.as_ref().map(|c| c.emitted),
        Some(3),
        "and the template's producer half"
    );
    assert_eq!(
        retained[&2].collapsed_enum_types,
        vec![MAINLINE_ENUM],
        "a mainline index: as before"
    );
    assert_eq!(retained[&2].drop_claim.as_ref().map(|c| c.emitted), Some(0));
    assert!(mir.is_empty(), "the MIR census map is drained");
}

/// Test 14: a capture refused at capture time — a lane refusal, a not-fully-lowered reason, a
/// sentinel module the binary writer refuses (trust-ir D1b) — stores only its reason, never the
/// module; a passing one stores it. The third capture-time gate, a reachable unsited check, is
/// test 9's.
#[test]
fn a_refused_capture_stores_no_module() {
    let lane = || {
        TemplateLane::new(
            rustc_middle::ty::TypingEnv::fully_monomorphized(),
            vec![(0, LaneParam::Type)],
        )
    };
    let passing = Lowered { module: calling_template_module(), ..clean_lowered() };
    let stored = StoredTemplate::of_lowering(&passing, &lane());
    assert_eq!(
        stored.module_bytes(),
        Some(
            trust_ir::binary::serialize_module(&passing.module)
                .expect("the control has a wire image")
                .len()
        ),
        "the control stores the module"
    );
    let loaded = stored.load().expect("loads");
    assert_eq!(loaded.capture.expect("captured").module, passing.module, "and it loads back");

    let mut refusing_lane = lane();
    refusing_lane.refuse("&T".to_string(), "parameter-dependent pointer metadata");
    let stored = StoredTemplate::of_lowering(&passing, &refusing_lane);
    assert_eq!(stored.module_bytes(), None);
    assert_eq!(
        stored.load().expect("loads").capture.expect_err("refused"),
        CaptureRefusal::Lane(vec!["parameter-dependent pointer metadata".to_string()])
    );

    let symbolic = Lowered { symbolic: true, ..passing.clone() };
    let stored = StoredTemplate::of_lowering(&symbolic, &lane());
    assert_eq!(stored.module_bytes(), None);
    assert_eq!(
        stored.load().expect("loads").capture.expect_err("refused"),
        CaptureRefusal::NotLowered(vec!["symbolic".to_string()])
    );

    // trust-ir D1b: no binary version carries a lexical-scope inlining chain, so the writer
    // refuses this module; the capture is a not-lowered reason and stores nothing (it never
    // panics, and it never stores a module the builder could not read back).
    let mut unencodable = passing.clone();
    unencodable.module.functions[0].scopes = Some(vec![trust_ir::ScopeData {
        parent: None,
        span: None,
        inlined_at: Some(trust_ir::InlinedAt {
            span: trust_ir::SourceSpan { file: 0, line: 1, col: 1 },
            callee: "dep::inlined".to_string(),
        }),
    }]);
    assert!(trust_ir::binary::serialize_module(&unencodable.module).is_err(), "the premise");
    let stored = StoredTemplate::of_lowering(&unencodable, &lane());
    assert_eq!(stored.module_bytes(), None);
    match stored.load().expect("loads").capture.expect_err("refused") {
        CaptureRefusal::NotLowered(reasons) => {
            assert_eq!(reasons.len(), 1, "{reasons:?}");
            assert!(
                reasons[0].starts_with("the per-body module has no wire image: "),
                "{reasons:?}"
            );
        }
        other => panic!("a refused wire image is a not-lowered reason: {other:?}"),
    }
}

#[test]
fn evidence_exact_store_arguments_roundtrip_and_reject_malformed_facts() {
    let mut evidence = sample_evidence();
    evidence.effects.push((EvidenceEffectKind::Store(u32::MAX), 4));
    evidence.exact_store_args = vec![(7, 1)];
    evidence.store_values = vec![(u32::MAX - 1, 2), (u32::MAX, 2)];
    assert_eq!(decode_evidence(&encode_evidence(&evidence)), Ok(evidence.clone()));
    for facts in [vec![(7, 2)], vec![(0, 1)], vec![(2, 1)], vec![(8, 1)], vec![(7, 1), (7, 0)]] {
        let mut bad = evidence.clone();
        bad.exact_store_args = facts;
        assert!(decode_evidence(&encode_evidence(&bad)).is_err());
    }
    let mut old = encode_evidence(&evidence);
    old[8..12].copy_from_slice(&3u32.to_le_bytes());
    assert_eq!(decode_evidence(&old), Err(EntryDecodeError::EvidenceSchema(3)));
}

struct ExactAbiNames(crate::calling_convention::FunctionAbi);
impl EntryNames for ExactAbiNames {
    fn body_symbol(&self) -> Result<String, String> {
        names().body_symbol()
    }
    fn body_abi(&self) -> crate::calling_convention::FunctionAbi {
        self.0
    }
    fn body_requires_caller_location(&self) -> bool {
        false
    }
    fn callee_symbol(&self, k: usize, c: &CalleeRef) -> Result<String, CalleeNameRefusal> {
        names().callee_symbol(k, c)
    }
    fn static_symbol(&self, d: DefId) -> Result<String, String> {
        names().static_symbol(d)
    }
    fn file_name(&self, p: &str) -> Result<String, String> {
        names().file_name(p)
    }
    fn target_info(&self) -> trust_ir::TargetInfo {
        names().target_info()
    }
}

struct ForeignPrototypeNames(FuncTy);
impl EntryNames for ForeignPrototypeNames {
    fn body_symbol(&self) -> Result<String, String> {
        names().body_symbol()
    }
    fn body_abi(&self) -> crate::calling_convention::FunctionAbi {
        crate::calling_convention::FunctionAbi::RUST
    }
    fn body_requires_caller_location(&self) -> bool {
        false
    }
    fn callee_symbol(&self, k: usize, c: &CalleeRef) -> Result<String, CalleeNameRefusal> {
        names().callee_symbol(k, c)
    }
    fn foreign_signature(&self, _: &CalleeRef) -> Option<FuncTy> {
        Some(self.0.clone())
    }
    fn static_symbol(&self, d: DefId) -> Result<String, String> {
        names().static_symbol(d)
    }
    fn file_name(&self, p: &str) -> Result<String, String> {
        names().file_name(p)
    }
    fn target_info(&self) -> trust_ir::TargetInfo {
        names().target_info()
    }
}

#[test]
fn metadata_entry_preserves_exact_variadic_prototype_without_claiming_a_foreign_body() {
    use trust_ir::signature_abi::*;
    let scalar = |place| AbiArgument {
        size: 4,
        align: 4,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister { class: AbiRegisterClass::Integer, bytes: 4 },
            source_offset: 0,
            source_bytes: 4,
            value_bits: 32,
            attributes: AbiAttributes::default(),
        }),
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: 4,
            carrier_offset: 0,
            carrier_bytes: 4,
        }],
    };
    let signature = FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: true,
        abi: Some(SignatureAbi {
            target: AbiTarget {
                triple: target().triple,
                data_layout: "e-p:64:64".into(),
                abi: String::new(),
                cpu: "generic".into(),
                features: vec![],
                target_spec: "source-target-fixture".into(),
                pointer_bytes: 8,
                little_endian: true,
            },
            frontend: AbiFrontend { name: "source-fixture".into(), revision: "1".into() },
            convention: "C".into(),
            lowered_convention: trust_ir::CallingConv::C,
            source_abi: "C".into(),
            can_unwind: false,
            variadic: true,
            fixed_count: 1,
            arguments: vec![scalar(AbiBindingPlace::Parameter(0))],
            result: scalar(AbiBindingPlace::Result(0)),
        }),
    };
    let mut c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    c.callees[0].params = crate::ParamSignature::Unsigned;
    c.callees[0].abi = crate::calling_convention::FunctionAbi::test_only_variadic(
        rustc_abi::ExternAbi::C { unwind: false },
        Some(rustc_abi::CanonAbi::C),
    );
    let entry = assemble_entry(&c, &ForeignPrototypeNames(signature.clone())).unwrap();
    let foreign = &entry.functions[1];
    assert!(foreign.is_declaration());
    assert_eq!(foreign.producer, None);
    assert_eq!(entry.func_type(foreign.ty), Some(&signature));
    let bytes = trust_ir::binary::serialize_module(&entry).unwrap();
    let decoded = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(decoded.func_type(decoded.functions[1].ty), Some(&signature));
    assert_eq!(entry.functions[0].blocks, c.module.functions[0].blocks);
    c.callees[0].params.withdraw();
    assert!(assemble_entry(&c, &ForeignPrototypeNames(signature.clone())).is_err());
    c.callees[0].params = crate::ParamSignature::Unsigned;
    c.callees[0].abi = crate::calling_convention::FunctionAbi::C;
    assert!(
        assemble_entry(&c, &ForeignPrototypeNames(signature)).is_err(),
        "a typed variadic prototype cannot contradict the original source's fixed signature"
    );
}

#[test]
fn exact_source_conventions_survive_body_and_metadata_declaration_extraction() {
    use rustc_abi::{CanonAbi, ExternAbi, X86Call};
    use trust_ir::CallingConv;

    use crate::calling_convention::FunctionAbi;
    for (source, canonical, expected) in [
        (ExternAbi::Rust, CanonAbi::Rust, CallingConv::Rust),
        (ExternAbi::C { unwind: false }, CanonAbi::C, CallingConv::C),
        (ExternAbi::C { unwind: true }, CanonAbi::C, CallingConv::CUnwind),
        (ExternAbi::System { unwind: false }, CanonAbi::X86(X86Call::Win64), CallingConv::Win64),
        (ExternAbi::SysV64 { unwind: false }, CanonAbi::X86(X86Call::SysV64), CallingConv::SysV64),
        (ExternAbi::RustCold, CanonAbi::RustCold, CallingConv::RustCold),
        (ExternAbi::Swift, CanonAbi::Swift, CallingConv::Swift),
    ] {
        let abi = FunctionAbi::test_only(source, Some(canonical));
        let mut c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
        c.module.functions[0].calling_conv = expected;
        c.callees[0].abi = abi;
        let entry = assemble_entry(&c, &ExactAbiNames(abi)).expect("exact source ABI");
        assert_eq!(entry.functions.len(), 2);
        assert_eq!(entry.functions[0].calling_conv, expected);
        assert_eq!(entry.functions[1].calling_conv, expected);
        assert_eq!(entry.functions[0].blocks, c.module.functions[0].blocks);
        assert_eq!(entry.func_type(entry.functions[1].ty).unwrap().params, vec![Ty::I32]);
        assert_eq!(entry.func_type(entry.functions[1].ty).unwrap().returns, vec![Ty::I32]);
    }
}

#[test]
fn metadata_refuses_same_shaped_wrong_abi_and_unsupported_source_protocols() {
    use rustc_abi::{CanonAbi, ExternAbi};

    use crate::calling_convention::FunctionAbi;
    let mut c = candidate(per_body_module(calling_body()), vec![callee(1, 9)]);
    assert_eq!(
        assemble_entry(&c, &ExactAbiNames(FunctionAbi::C)).unwrap_err(),
        EntryRefusal::Invalid("judged body and source calling convention disagree".into())
    );
    let rust_call = FunctionAbi::test_only(ExternAbi::RustCall, Some(CanonAbi::Rust));
    assert!(assemble_entry(&c, &ExactAbiNames(rust_call)).is_err());
    for abi in [FunctionAbi::UNKNOWN, FunctionAbi::CONFLICT, rust_call] {
        c.callees[0].abi = abi;
        assert_eq!(
            assemble_entry(&c, &ExactAbiNames(FunctionAbi::RUST)).unwrap_err(),
            EntryRefusal::Invalid(
                "unsupported, absent or conflicting source calling convention".into()
            )
        );
    }
}

#[test]
fn a_template_hole_cannot_hide_an_unsupported_or_different_source_protocol() {
    use rustc_abi::{CanonAbi, ExternAbi};

    use crate::calling_convention::FunctionAbi;
    use crate::template_key::{HoleKey, KeyArg, KeyTy};
    let mut c = template_candidate(calling_template_module(), vec![callee(1, 9)]);
    c.facts.owner = Some((7, 8));
    c.facts.parameter_indices = vec![0];
    c.facts.callee_holes.push(crate::template_lowering::CalleeHole {
        id: trust_ir::HoleId::new(0),
        decl: FuncId::new(1),
        key: HoleKey::Callee { item: (1, 9), args: vec![KeyArg::Type(KeyTy::Param(0))] },
        signature: FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        },
        dependencies: vec![(
            0,
            trust_ir::template::TemplateArg::Type(trust_ir::TyG::Ext(
                trust_ir::TemplateRef::Param(trust_ir::ParamId::new(0)),
            )),
        )],
    });
    crate::template_lowering::pending::assemble(&c, &names(), "abi-hole".into())
        .expect("complete plain-Rust hole control");
    for abi in [
        FunctionAbi::C,
        FunctionAbi::UNKNOWN,
        FunctionAbi::CONFLICT,
        FunctionAbi::test_only(ExternAbi::RustCall, Some(CanonAbi::Rust)),
    ] {
        c.callees[0].abi = abi;
        let error = crate::template_lowering::pending::assemble(&c, &names(), "abi-hole".into())
            .err()
            .expect("a neutral hole is not an ABI adapter");
        assert_eq!(
            error,
            EntryRefusal::Invalid(
                "callee hole source calling convention requires an adapter".into()
            )
        );
    }
}

#[test]
fn source_entry_requires_the_original_owner_and_checks_the_complete_source_section() {
    use crate::source_word64::{Operand, record};
    let module =
        assemble_entry(&candidate(per_body_module(mix_body()), Vec::new()), &names()).unwrap();
    let binding = EntryBinding { stable_crate_id: 1, local_hash: 2 };
    let source = record::Record {
        owner: record::Definition { stable_crate_id: 1, local_hash: 2 },
        parameters: vec![4],
        expressions: 3,
        source_hash: "actual-source-claim".into(),
        body: record::Body::Operand { node: 0, value: Operand::Parameter(0) },
    };
    let good = frame_entry_with_source(&module, binding, true, &[], Some(&source)).unwrap();
    assert_eq!(decode_entry(&good).unwrap().source, Some(source.clone()));
    assert!(
        decode_entry(&frame_entry(&module, binding, true, &[]).unwrap()).unwrap().source.is_none()
    );
    let mut wrong = source.clone();
    wrong.owner.local_hash += 1;
    assert!(frame_entry_with_source(&module, binding, true, &[], Some(&wrong)).is_err());
    // Replace the source bytes with a canonical record for the wrong owner and
    // recompute the envelope digest: semantic owner checking must still refuse.
    let source_wire = record::encode(&wrong).unwrap();
    let mut bad = good.clone();
    let start = bad.len() - source_wire.len();
    bad[start..].copy_from_slice(&source_wire);
    let digest = entry_content_digest(&bad[..16], &bad[56..]).unwrap();
    bad[16..48].copy_from_slice(&digest);
    assert!(matches!(decode_entry(&bad), Err(EntryDecodeError::Source(_))));
    // No recomputation: changing source bytes must fail the complete digest.
    let mut bad = good;
    *bad.last_mut().unwrap() ^= 1;
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::EnvelopeDigest);
}
