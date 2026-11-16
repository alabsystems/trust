//! Trust (step 2 increment 5, sub-step 5.4.2): the rules of `codegen_module.rs`, each over a
//! hand-built producer module. Every test names the rule it pins; each fails without that rule
//! (the edge-retarget, handoff-differs-in-star and proof-tables-stripped cases were measured
//! failing with their rule disabled, and after the review the reserved-name, self-edge,
//! two-caller self-edge and `bool`-parameter cases — docs/DECISION_QUEUE.md, INC5.4-FREEZE).
//!
//! PURE: no `TyCtxt`. `AbiShape`s are written by hand in the shape `abi_shape::abi_shape_of`
//! reads from rustc's `FnAbi`.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_bridge::call_event::{AbiExt, ParamPlace, ReturnPlace, ScalarPlace, Slot};
use trust_cg_bridge::codegen_backend::FunctionLinkage;
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{
    Block, BodyGate, Constant, DropGlueEntry, FatPtrKind, FieldDef, Function, FunctionSummary,
    Global, Linkage, Module, ObligationKind, ParamAttrs, Producer, ProofObligation, ProofStatus,
    StructDef, StructId, StructRepr, Ty, Visibility,
};

use super::super::RefusalClass;
use super::super::abi_shape::{
    AbiConv, AbiExtension, AbiShape, ArgShape, PairOf, ScalarKind, ScalarShape,
};
use super::*;

const TRIPLE: &str = "arm64-apple-macosx11.0.0";
const DIRECT: &str = "trust-direct-lane-structural";

fn direct(bits: u32) -> ArgShape {
    ArgShape::Direct {
        bits,
        kind: ScalarKind::Int { signed: false },
        ext: AbiExtension::None,
        inreg: false,
        audited: true,
        newtype: false,
    }
}

fn abi(params: Vec<ArgShape>, ret: ArgShape) -> AbiShape {
    AbiShape { conv: AbiConv::Rust, params, ret }
}

/// `(u64) -> u64`, as rustc passes it.
fn u64_abi() -> AbiShape {
    abi(vec![direct(64)], direct(64))
}

/// A producer module and the inputs `build` reads.
struct Fixture {
    m: Module,
    base: Option<Module>,
    items: Vec<WorkItem>,
    residue: BTreeMap<FuncId, ResidueIdentity>,
    declarations: BTreeMap<String, AbiShape>,
    statics: Vec<CollectorStatic>,
    target: ExpectedTarget,
    sig: FuncTyId,
}

impl Fixture {
    fn new() -> Self {
        let mut m = Module::new("k");
        m.target_info = Some(trust_ir::TargetInfo {
            triple: TRIPLE.to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        let sig = m
            .add_func_type(FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        Fixture {
            m,
            base: None,
            items: Vec::new(),
            residue: BTreeMap::new(),
            declarations: BTreeMap::new(),
            statics: Vec::new(),
            target: ExpectedTarget { triple: TRIPLE.to_string(), pointer_size: 8 },
            sig,
        }
    }

    /// `name(x: u64) -> u64`: calls each of `callees` in turn on the previous result.
    fn body(&mut self, name: &str, callees: &[FuncId]) -> FuncId {
        let id = FuncId::new(self.m.functions.len() as u32);
        let mut f = Function::new(id, name, self.sig, BlockId::new(0));
        let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
        let mut last = ValueId::new(0);
        for (i, callee) in callees.iter().enumerate() {
            let result = ValueId::new(i as u32 + 1);
            b.body.push(
                InstrNode::new(Inst::Call { callee: *callee, args: vec![last] })
                    .with_result(result),
            );
            last = result;
        }
        b.body.push(InstrNode::new(Inst::Return { values: vec![last] }));
        f.blocks.push(b);
        f.producer = Some(Producer::TRust);
        f.body_gate = Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
        self.m.try_add_function(f).expect("Module::try_add_function: test fixture");
        id
    }

    /// `name(params..) -> ret`, returning the constant `value`.
    fn body_sig(&mut self, name: &str, params: Vec<Ty>, ret: Ty, value: Constant) -> FuncId {
        let sig = self
            .m
            .add_func_type(FuncTy {
                params: params.clone(),
                returns: vec![ret.clone()],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let id = FuncId::new(self.m.functions.len() as u32);
        let mut f = Function::new(id, name, sig, BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        for (i, ty) in params.iter().enumerate() {
            b = b.with_param(ValueId::new(i as u32), ty.clone());
        }
        let result = ValueId::new(params.len() as u32);
        b.body.push(InstrNode::new(Inst::Const { ty: ret, value }).with_result(result));
        b.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
        f.blocks.push(b);
        f.producer = Some(Producer::TRust);
        f.body_gate = Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
        self.m.try_add_function(f).expect("Module::try_add_function: test fixture");
        id
    }

    /// A bodyless `(u64) -> u64` declaration.
    fn decl(&mut self, name: &str) -> FuncId {
        let id = FuncId::new(self.m.functions.len() as u32);
        let mut f = Function::new(id, name, self.sig, BlockId::new(0));
        f.producer = Some(Producer::TRust);
        self.m.try_add_function(f).expect("Module::try_add_function: test fixture");
        id
    }

    /// The producer function `id`, for edits.
    fn function_mut(&mut self, id: FuncId) -> &mut Function {
        self.m.functions.iter_mut().find(|f| f.id == id).expect("a function")
    }

    fn item(&mut self, symbol: &str, func: FuncId) {
        self.items.push(WorkItem {
            symbol: symbol.to_string(),
            func,
            linkage: FunctionLinkage::External,
            never_inline: false,
            handoff: false,
            state: WorkState::Admitted { abi: u64_abi() },
        });
    }

    fn input(&self) -> CodegenModuleInput<'_> {
        CodegenModuleInput {
            handoff_extensions: None,
            producer: &self.m,
            base: self.base.as_ref(),
            items: &self.items,
            residue: &self.residue,
            declarations: &self.declarations,
            statics: &self.statics,
            target: &self.target,
        }
    }

    fn run(&self) -> CodegenModuleOutput {
        build(&self.input())
    }
}

fn names(out: &CodegenModuleOutput) -> Vec<&str> {
    out.m_cg.functions.iter().map(|f| f.name.as_str()).collect()
}

fn find<'a>(out: &'a CodegenModuleOutput, symbol: &str) -> &'a Function {
    out.m_cg
        .functions
        .iter()
        .find(|f| f.name == symbol)
        .unwrap_or_else(|| panic!("M_cg has no `{symbol}`: {:?}", names(out)))
}

/// The refusals rendered, one per line, for assertion messages and needles.
fn rendered(out: &CodegenModuleOutput) -> String {
    out.refusals.iter().map(|r| r.to_string()).collect::<Vec<_>>().join("\n")
}

fn refused_with(out: &CodegenModuleOutput, class: RefusalClass, symbol: &str, needle: &str) {
    assert!(
        out.refusals.iter().any(|r| r.class() == class
            && r.sample_line().contains(symbol)
            && r.to_string().contains(needle)),
        "no [{}] refusal of `{symbol}` containing `{needle}`:\n{}",
        class.tag(),
        rendered(out)
    );
}

fn clean(out: &CodegenModuleOutput) {
    assert!(out.refusals.is_empty(), "unexpected refusals:\n{}", rendered(out));
}

// ---- rules 1, 5: names and the map ----------------------------------------------------------

/// Rule 5: every M_cg body carries its link symbol, its call edge names the callee's M_cg id,
/// and the gate's `bodies` map the symbol back to the producer body.
#[test]
fn every_emitted_body_is_named_by_its_symbol() {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let f = fx.body("crate::f", &[g]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    let out = fx.run();
    clean(&out);
    assert_eq!(names(&out), ["_RF", "_RG"], "work-list order");
    let mf = find(&out, "_RF");
    let mg = find(&out, "_RG");
    assert_eq!(mf.display_path.as_deref(), Some("crate::f"));
    match &mf.blocks[0].body[0].inst {
        Inst::Call { callee, .. } => assert_eq!(*callee, mg.id, "the edge names g's M_cg id"),
        other => panic!("{other:?}"),
    }
    assert_eq!(out.bodies["_RF"].func, f);
    assert_eq!(out.bodies["_RG"].func, g);
    assert_eq!(out.symbols[&f], "_RF");
    assert_eq!(out.symbols[&g], "_RG");
    // Dense ids.
    let ids: Vec<u32> = out.m_cg.functions.iter().map(|f| f.id.index()).collect();
    assert_eq!(ids, [0, 1]);
}

/// Rule 1: FuncId <-> symbol is injective; two bodies under one symbol, or one body under two
/// symbols, refuse.
#[test]
fn funcid_symbol_map_is_injective() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    fx.item("_RF2", f);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF2", "injective");
    assert!(!names(&out).contains(&"_RF2"));

    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    let g = fx.body("crate::g", &[]);
    fx.item("_RX", f);
    fx.item("_RX", g);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RX", "injective");
    assert!(names(&out).is_empty(), "neither body ships under the contested symbol");
}

/// Rule 13: retarget an edge BETWEEN `assemble` and `check_postcondition`; the postcondition
/// must name the edge. Without the rule (MEASURED, INC5.4-FREEZE) the retargeted module passes.
#[test]
fn every_call_edge_names_the_resolved_instance_symbol() {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let h = fx.body("crate::h", &[]);
    let f = fx.body("crate::f", &[g]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    fx.item("_RH", h);
    let input = fx.input();
    let mut assembled = assemble(&input);
    assert!(check_postcondition(&input, &assembled).is_empty(), "the unmutated module passes");
    let h_id = assembled.output.m_cg.functions.iter().find(|f| f.name == "_RH").unwrap().id;
    let f_body = assembled.output.m_cg.functions.iter_mut().find(|f| f.name == "_RF").unwrap();
    let Inst::Call { callee, .. } = &mut f_body.blocks[0].body[0].inst else { panic!() };
    *callee = h_id;
    let post = check_postcondition(&input, &assembled);
    assert!(
        post.iter().any(|r| r.class() == RefusalClass::CodegenModule
            && r.to_string().contains("names `_RH`, but the resolved instance there is `_RG`")),
        "the retargeted edge must be refused: {:?}",
        post.iter().map(|r| r.to_string()).collect::<Vec<_>>()
    );
}

/// Rule 2: a body no admitted item reaches is not in M_cg.
#[test]
fn unreachable_bodies_are_pruned() {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let _unreached = fx.body("crate::unreached", &[]);
    let f = fx.body("crate::f", &[g]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    let out = fx.run();
    clean(&out);
    assert_eq!(out.m_cg.functions.len(), 2, "{:?}", names(&out));
    assert!(
        !out.m_cg.functions.iter().any(|f| f.display_path.as_deref() == Some("crate::unreached"))
    );
    assert!(residue_candidates(&fx.m, &BTreeSet::from([f])).contains(&g));
    assert!(residue_candidates(&fx.m, &BTreeSet::from([f, g])).is_empty());
}

// ---- rule 2: inventory residue --------------------------------------------------------------

/// Rule 2: a reached local helper rustc's inventory does not name is emitted `Internal` under
/// its own symbol, placed, and disclosed.
#[test]
fn local_residue_is_emitted_internal_and_disclosed() {
    let mut fx = Fixture::new();
    let h = fx.body("crate::helper", &[]);
    let f = fx.body("crate::f", &[h]);
    fx.item("_RF", f);
    fx.residue.insert(
        h,
        ResidueIdentity::Local { symbol: "_RHelper".into(), abi: u64_abi(), never_inline: false },
    );
    let out = fx.run();
    clean(&out);
    let helper = find(&out, "_RHelper");
    assert_eq!((helper.linkage, helper.visibility), (Linkage::Internal, Visibility::Default));
    assert_eq!(out.residue.len(), 1);
    assert_eq!(out.residue[0].symbol, "_RHelper");
    assert_eq!(out.residue[0].producer_func, h);
    assert!(out.placements.contains_key("_RHelper"));
    assert_eq!(out.symbols[&h], "_RHelper");

    // Without an identity the residue (and its caller) refuse.
    fx.residue.clear();
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "crate::helper", "no identity");
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "which is refused");
    assert!(names(&out).is_empty());
}

/// Rule 2: upstream residue refuses `[upstream-body]`, residue the instance lane spliced
/// refuses `[codegen-module]` (INC5.4-SCOPE), and both drop their caller.
#[test]
fn upstream_residue_is_refused() {
    let mut fx = Fixture::new();
    let h = fx.body("core::helper", &[]);
    let f = fx.body("crate::f", &[h]);
    fx.item("_RF", f);
    fx.residue.insert(
        h,
        ResidueIdentity::Upstream {
            symbol: "_RCoreHelper".into(),
            def_path: "core::helper".into(),
            krate: "core".into(),
        },
    );
    let out = fx.run();
    refused_with(&out, RefusalClass::UpstreamBody, "_RCoreHelper", "core");
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "which is refused");
    assert!(names(&out).is_empty());

    fx.residue.insert(h, ResidueIdentity::InstanceSpliced { symbol: "_RSpliced".into() });
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RSpliced", "INC5.4-SCOPE");
}

// ---- rule 3: declarations -------------------------------------------------------------------

/// Rule 3: a reserved name refuses EVEN WHEN the declaration map gives it an entry with a
/// matching `AbiShape` (the 5.6 shape the rule exists for), and a name with no entry refuses.
/// Each needle is unique to its own refusal, so removing the reserved-prefix check fails the
/// first loop (the name then binds as an ordinary External declaration).
#[test]
fn reserved_declaration_names_refuse() {
    for name in [
        "!trust_unresolved_callee::0",
        "!trust_bodyless_instance::1",
        "!trust_conflicting_declaration::2",
        "!trust_definition::3",
    ] {
        let mut fx = Fixture::new();
        let d = fx.decl(name);
        let f = fx.body("crate::f", &[d]);
        fx.item("_RF", f);
        fx.declarations.insert(name.into(), u64_abi());
        let out = fx.run();
        refused_with(&out, RefusalClass::CodegenModule, "_RF", "name is reserved and carries no");
        refused_with(&out, RefusalClass::CodegenModule, "_RF", name);
        assert!(names(&out).is_empty(), "{name}: {:?}", names(&out));
        assert!(!out.symbols.values().any(|s| s == name), "{name} got no link symbol");
    }
    let mut fx = Fixture::new();
    let d = fx.decl("libc::fcntl");
    let f = fx.body("crate::f", &[d]);
    fx.item("_RF", f);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "the declaration map is empty until");
    assert!(names(&out).is_empty());
}

/// Rule 3: `!trust_self_edge::k` binds to the calling body. The producer ids are offset (an
/// unreached body first), so neither the declaration's nor the caller's producer `FuncId`
/// equals the caller's M_cg id 0: without the remap the edge keeps a stale id and this fails.
#[test]
fn self_edge_binds_to_the_calling_body() {
    let mut fx = Fixture::new();
    let _unreached = fx.body("crate::unreached", &[]);
    let d = fx.decl("!trust_self_edge::0");
    let f = fx.body("crate::f", &[d]);
    assert!(d.index() != 0 && f.index() != 0);
    fx.item("_RF", f);
    let out = fx.run();
    clean(&out);
    assert_eq!(names(&out), ["_RF"], "the unreached body is pruned");
    let mf = find(&out, "_RF");
    assert_eq!(mf.id.index(), 0);
    let Inst::Call { callee, .. } = &mf.blocks[0].body[0].inst else { panic!() };
    assert_eq!(*callee, mf.id, "the self edge binds to the body itself");
    assert_eq!(out.symbols[&d], "_RF", "S(self edge) is the caller's symbol");
}

/// Rule 3: a self edge names exactly one body, so one called by two bodies binds to neither:
/// BOTH callers refuse (the first one bound it before the second was seen).
#[test]
fn self_edge_called_by_two_bodies_binds_to_neither() {
    let mut fx = Fixture::new();
    let d = fx.decl("!trust_self_edge::0");
    let f = fx.body("crate::f", &[d]);
    let g = fx.body("crate::g", &[d]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "binds to neither");
    refused_with(&out, RefusalClass::CodegenModule, "_RG", "binds to neither");
    assert!(names(&out).is_empty(), "{:?}", names(&out));
}

/// Rule 3 (dormant until 5.6): a declaration's FuncTy must equal rustc's FnAbi-legalized
/// signature; a matching one is an External declaration with its own P.
#[test]
fn callee_abi_mismatch_refuses_a_declaration() {
    let mut fx = Fixture::new();
    let d = fx.decl("ext_fn");
    let f = fx.body("crate::f", &[d]);
    fx.item("_RF", f);
    fx.declarations.insert("ext_fn".into(), abi(vec![direct(32)], direct(64)));
    let out = fx.run();
    refused_with(&out, RefusalClass::CalleeAbiMismatch, "_RF", "ext_fn");

    fx.declarations.insert("ext_fn".into(), u64_abi());
    let out = fx.run();
    clean(&out);
    let decl = find(&out, "ext_fn");
    assert!(decl.is_declaration());
    assert_eq!(decl.linkage, Linkage::External);
    assert!(out.placements.contains_key("ext_fn"));
    assert_eq!(out.symbols[&d], "ext_fn");
}

// ---- rules 4, 12: producers and body gates --------------------------------------------------

/// Rule 12: the gate is copied verbatim (an `Ungated` body stays `Ungated` for trust-cg's
/// license to refuse), and a gate changed after assembly is refused by the postcondition.
#[test]
fn body_gates_are_copied_not_laundered() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.function_mut(f).body_gate = Some(BodyGate::Ungated);
    fx.item("_RF", f);
    let out = fx.run();
    clean(&out);
    assert_eq!(find(&out, "_RF").body_gate, Some(BodyGate::Ungated));
    fx.function_mut(f).body_gate = None;
    let out = fx.run();
    assert_eq!(find(&out, "_RF").body_gate, None, "no claim stays no claim");

    let input = fx.input();
    let mut assembled = assemble(&input);
    assembled.output.m_cg.functions[0].body_gate =
        Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
    let post = check_postcondition(&input, &assembled);
    assert!(
        post.iter().any(|r| r.to_string().contains("differs from its producer body")),
        "a restamped gate must be refused"
    );
}

/// Rule 4: a Clean-origin body keeps its named refusal; every non-Rust producer refuses.
#[test]
fn clean_origin_body_refuses() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.function_mut(f).producer = Some(Producer::Clean);
    fx.item("_RF", f);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "CleanOriginBelowCodegenGate");
    for producer in [
        None,
        Some(Producer::TrustIr),
        Some(Producer::TC),
        Some(Producer::Other("rust-generated-coroutine-mir.scalar-copy.v1".into())),
    ] {
        fx.function_mut(f).producer = producer.clone();
        let out = fx.run();
        refused_with(&out, RefusalClass::CodegenModule, "_RF", "INC5.4-PRODUCER");
        assert!(names(&out).is_empty(), "{producer:?}");
    }
    // A Clean-origin body reached as inventory residue keeps the named refusal too, whatever
    // the rustc half could say about its identity, and its caller is dropped.
    let mut fx = Fixture::new();
    let clean = fx.body("m::cleanWsum", &[]);
    fx.function_mut(clean).producer = Some(Producer::Clean);
    let caller = fx.body("crate::calls_clean", &[clean]);
    fx.item("_RCallsClean", caller);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "m::cleanWsum", "CleanOriginBelowCodegenGate");
    refused_with(&out, RefusalClass::CodegenModule, "_RCallsClean", "which is refused");
    assert!(names(&out).is_empty());
}

/// Candidate assembly is separate from the bridge's live-token admission.
/// The ordinary assembler stays closed, and the candidate path retains the
/// exact carrier stamp rather than converting it to a Rust authority.
#[test]
fn clean_candidate_requires_its_stamp_and_preserves_the_identity_body() {
    let mut fx = Fixture::new();
    let f = fx.body("_RF", &[]);
    fx.function_mut(f).producer = Some(Producer::Clean);
    fx.item("_RF", f);
    let candidates = BTreeSet::from([f]);
    for stamp in [
        None,
        Some(BodyGate::Ungated),
        Some(BodyGate::Gated { authority: DIRECT.into(), evidence: None }),
    ] {
        fx.function_mut(f).body_gate = stamp;
        let out = build_with_clean_candidates(&fx.input(), &candidates);
        refused_with(&out, RefusalClass::CodegenModule, "_RF", "CleanOriginBelowCodegenGate");
    }
    fx.function_mut(f).body_gate = Some(trust_clean_ir_gate::clean_carrier_gate_stamp());
    refused_with(&fx.run(), RefusalClass::CodegenModule, "_RF", "CleanOriginBelowCodegenGate");
    let out = build_with_clean_candidates(&fx.input(), &candidates);
    clean(&out);
    let body = find(&out, "_RF");
    let source = fx.m.function_by_id(f).expect("source");
    assert_eq!(body.producer, Some(Producer::Clean));
    assert_eq!(body.body_gate, source.body_gate);
    assert_eq!(body.ty, source.ty);
    assert_eq!(body.blocks, source.blocks);
}

#[test]
fn clean_candidates_cannot_inherit_the_rust_abi_rewrite_rule() {
    let mut fx = Fixture::new();
    let f = fx.func("_RF", vec![Ty::U64, Ty::Unit], vec![Ty::U64], vec![ret(&[0])]);
    fx.function_mut(f).producer = Some(Producer::Clean);
    fx.function_mut(f).body_gate = Some(trust_clean_ir_gate::clean_carrier_gate_stamp());
    fx.item_abi("_RF", f, abi(vec![direct(64), ArgShape::Ignore], direct(64)));
    let out = build_with_clean_candidates(&fx.input(), &BTreeSet::from([f]));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "identity ABI");
    assert!(names(&out).is_empty());
}

// ---- rules 6, 8 ----------------------------------------------------------------------------

/// Rule 6: rustc's linkage and visibility, exactly.
#[test]
fn linkage_matches_rustc() {
    let mut fx = Fixture::new();
    let a = fx.body("crate::a", &[]);
    let b = fx.body("crate::b", &[]);
    let c = fx.body("crate::c", &[]);
    for (symbol, func, linkage) in [
        ("_RA", a, FunctionLinkage::External),
        ("_RB", b, FunctionLinkage::Hidden),
        ("_RC", c, FunctionLinkage::Internal),
    ] {
        fx.item(symbol, func);
        fx.items.last_mut().unwrap().linkage = linkage;
    }
    let out = fx.run();
    clean(&out);
    let got = |s| {
        let f = find(&out, s);
        (f.linkage, f.visibility)
    };
    assert_eq!(got("_RA"), (Linkage::External, Visibility::Default));
    assert_eq!(got("_RB"), (Linkage::External, Visibility::Hidden));
    assert_eq!(got("_RC"), (Linkage::Internal, Visibility::Default));
}

fn global(name: &str, linkage: Linkage, mutable: bool, initializer: Option<Constant>) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::U64,
        mutable,
        initializer,
        linkage,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// Rule 8: statics are one-to-one with the collector by symbol; a module-local constant is
/// fine, an exported global the collector does not name, a mutable or an imported one refuses.
#[test]
fn statics_match_the_collector_one_to_one() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    fx.m.globals.push(global(
        "__trust_promoted_0",
        Linkage::Internal,
        false,
        Some(Constant::Int(7)),
    ));
    clean(&fx.run());

    fx.statics.push(CollectorStatic {
        symbol: "_RSTATIC".into(),
        mutable: false,
        is_external: true,
    });
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RSTATIC", "one-to-one with the collector");

    fx.m.globals.push(global("_RSTATIC", Linkage::External, false, Some(Constant::Int(1))));
    clean(&fx.run());

    fx.m.globals.push(global("_RLOOSE", Linkage::External, false, Some(Constant::Int(1))));
    refused_with(&fx.run(), RefusalClass::CodegenModule, "_RLOOSE", "not one of rustc's");
    fx.m.globals.pop();
    fx.m.globals.push(global(
        "__trust_static_0__m",
        Linkage::Internal,
        true,
        Some(Constant::Int(1)),
    ));
    refused_with(&fx.run(), RefusalClass::CodegenModule, "__trust_static_0__m", "mutable");
    fx.m.globals.pop();
    fx.m.globals.push(global("__trust_staticaddr_0__x", Linkage::External, false, None));
    refused_with(&fx.run(), RefusalClass::CodegenModule, "__trust_staticaddr_0__x", "imported");
}

/// Rule 7: the target is stamped `Unclassified` for this triple; anything else refuses.
#[test]
fn target_info_is_stamped_unclassified_for_this_target() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    clean(&fx.run());
    fx.m.target_info.as_mut().unwrap().struct_passing = trust_ir::StructPassingPolicy::NativeC;
    refused_with(&fx.run(), RefusalClass::CodegenModule, "k", "unclassified");
    fx.m.target_info.as_mut().unwrap().struct_passing = trust_ir::StructPassingPolicy::Unclassified;
    fx.target.triple = "aarch64-unknown-linux-gnu".into();
    refused_with(&fx.run(), RefusalClass::CodegenModule, "k", "this compilation's");
    fx.m.target_info = None;
    refused_with(&fx.run(), RefusalClass::CodegenModule, "k", "no `target_info`");
}

// ---- rule 9: the scalar subset --------------------------------------------------------------

fn single(fx: &mut Fixture, shape: AbiShape) -> CodegenModuleOutput {
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    fx.items.last_mut().unwrap().state = WorkState::Admitted { abi: shape };
    fx.run()
}

/// Rule 9: `Cast` and by-value stack refuse for all of 5.4. Since 5.4.3 an `Indirect` or
/// `Ignore` slot is legalized, but only for a producer type it can be the legalization of: a
/// `u64` rustc passes indirectly (or not at all) is a genuine disagreement, and an `Indirect`
/// slot the old lane's by-value-struct predicate does not admit stays refused.
#[test]
fn cast_and_byval_refuse() {
    for (shape, needle) in [
        (ArgShape::Cast, "`Cast`"),
        (
            ArgShape::Indirect { on_stack: true, has_meta: false, audited: false },
            "by value on the stack",
        ),
        (
            ArgShape::Indirect { on_stack: false, has_meta: false, audited: true },
            "rustc passes a by-value struct indirectly, but the producer's type is U64",
        ),
        (
            ArgShape::Indirect { on_stack: false, has_meta: false, audited: false },
            "not a by-value struct of more than 16 bytes",
        ),
        (ArgShape::Indirect { on_stack: false, has_meta: true, audited: false }, "with metadata"),
        (ArgShape::Ignore, "is not zero-sized"),
    ] {
        let out = single(&mut Fixture::new(), abi(vec![shape], direct(64)));
        refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", needle);
        assert!(names(&out).is_empty());
    }
    let out = single(&mut Fixture::new(), abi(vec![direct(64)], ArgShape::Cast));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "the result");
}

/// Rule 9: a `Sext` argument and a `Zext` on a non-`bool` result refuse.
#[test]
fn ext_bearing_slot_refuses() {
    let sext = ArgShape::Direct {
        bits: 64,
        kind: ScalarKind::Int { signed: true },
        ext: AbiExtension::Sext,
        inreg: false,
        audited: true,
        newtype: false,
    };
    let out = single(&mut Fixture::new(), abi(vec![sext], direct(64)));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "extension");
    let zext_ret = ArgShape::Direct {
        bits: 64,
        kind: ScalarKind::Int { signed: false },
        ext: AbiExtension::Zext,
        inreg: false,
        audited: true,
        newtype: false,
    };
    let out = single(&mut Fixture::new(), abi(vec![direct(64)], zext_ret));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "the result");
    // An un-audited slot (`&mut T`, a raw pointer, a float) refuses too.
    let unaudited = ArgShape::Direct {
        bits: 64,
        kind: ScalarKind::Pointer,
        ext: AbiExtension::None,
        inreg: false,
        audited: false,
        newtype: false,
    };
    let out = single(&mut Fixture::new(), abi(vec![unaudited], direct(64)));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "audited register lane");
    // A width disagreement between rustc and the producer refuses.
    let out = single(&mut Fixture::new(), abi(vec![direct(32)], direct(64)));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "rustc's slot 32");
}

/// Rule 9 and 10 for `bool` (INC5.4-BOOLRET): the result is admitted with P `Zext` at 32 bits;
/// a `bool` parameter refuses.
#[test]
fn bool_return_is_admitted_with_zext_placement() {
    let mut fx = Fixture::new();
    let f = fx.body_sig("crate::is_odd", vec![Ty::U64], Ty::Bool, Constant::Bool(true));
    fx.item("_RIsOdd", f);
    let zext_bool = ArgShape::Direct {
        bits: 8,
        kind: ScalarKind::Int { signed: false },
        ext: AbiExtension::Zext,
        inreg: false,
        audited: true,
        newtype: false,
    };
    fx.items[0].state = WorkState::Admitted { abi: abi(vec![direct(64)], zext_bool.clone()) };
    let out = fx.run();
    clean(&out);
    assert_eq!(
        out.placements["_RIsOdd"].ret,
        ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::Zext })
    );
    // The result's `Zext` is admitted for `bool` only (a byte, zero-extended).
    fx.items[0].state = WorkState::Admitted { abi: abi(vec![direct(64)], direct(8)) };
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RIsOdd", "zero-extended byte");

    let mut fx = Fixture::new();
    let f = fx.body_sig("crate::takes_bool", vec![Ty::Bool], Ty::U64, Constant::Int(0));
    fx.item("_RTakesBool", f);
    fx.items[0].state = WorkState::Admitted { abi: abi(vec![zext_bool], direct(64)) };
    // The needle is the explicit check's own (SUBSET_NOTE also says "`bool` parameters").
    refused_with(
        &fx.run(),
        RefusalClass::UnsupportedAbi,
        "_RTakesBool",
        "caller-side `Zext` promise is not modeled",
    );
}

// ---- rule 10: P ----------------------------------------------------------------------------

/// Rule 10: integers take X0.., a 128-bit value the next even pair, at most 8 registers; a
/// function past the register file gets no entry. A float gets none from `placement` either,
/// but through `build` it never reaches P: rule 9 refuses it `[unsupported-abi]` first, as
/// rustc reads it (`audited: false`, the register lane has no float) and as an audited slot.
#[test]
fn placement_follows_aapcs64_gprs() {
    let mut fx = Fixture::new();
    let f = fx.body_sig("crate::f", vec![Ty::U64, Ty::U128, Ty::U32], Ty::U64, Constant::Int(0));
    let shape = abi(vec![direct(64), direct(128), direct(32)], direct(64));
    let function = fx.m.function_by_id(f).unwrap().clone();
    let p = placement(&fx.m, &function, &shape).expect("placed");
    assert_eq!(
        p.params,
        vec![
            ParamPlace::Scalar(ScalarPlace::gpr(0, 64)),
            ParamPlace::Scalar(ScalarPlace {
                slot: Slot::GprPair { lo: 2, hi: 3 },
                width: 128,
                ext: AbiExt::None
            }),
            ParamPlace::Scalar(ScalarPlace::gpr(4, 32)),
        ]
    );
    assert_eq!(p.ret, ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)));

    let nine = fx.body_sig("crate::nine", vec![Ty::U64; 9], Ty::U64, Constant::Int(0));
    let nine = fx.m.function_by_id(nine).unwrap().clone();
    assert!(placement(&fx.m, &nine, &abi(vec![direct(64); 9], direct(64))).is_none());
    let eight = fx.body_sig("crate::eight", vec![Ty::U64; 8], Ty::U64, Constant::Int(0));
    let eight = fx.m.function_by_id(eight).unwrap().clone();
    assert!(placement(&fx.m, &eight, &abi(vec![direct(64); 8], direct(64))).is_some());
    let float = ArgShape::Direct {
        bits: 64,
        kind: ScalarKind::Float,
        ext: AbiExtension::None,
        inreg: false,
        audited: true,
        newtype: false,
    };
    assert!(
        placement(&fx.m, &function, &abi(vec![float, direct(128), direct(32)], direct(64)))
            .is_none()
    );

    // Through `build`: the item ships with its P; a nine-argument item ships with none.
    fx.item("_RF", f);
    fx.items[0].state = WorkState::Admitted { abi: shape };
    fx.items.push(WorkItem {
        symbol: "_RNine".into(),
        func: nine.id,
        linkage: FunctionLinkage::External,
        never_inline: false,
        handoff: false,
        state: WorkState::Admitted { abi: abi(vec![direct(64); 9], direct(64)) },
    });
    let out = fx.run();
    clean(&out);
    assert_eq!(out.placements["_RF"], p);
    assert!(!out.placements.contains_key("_RNine"), "past the register file: no P, Unknown");
    assert!(names(&out).contains(&"_RNine"), "but it is still compiled (no register cap)");

    for audited in [false, true] {
        let mut fx = Fixture::new();
        let fadd = fx.body_sig("crate::fadd", vec![Ty::F64], Ty::U64, Constant::Int(0));
        fx.item("_RFadd", fadd);
        let float = ArgShape::Direct {
            bits: 64,
            kind: ScalarKind::Float,
            ext: AbiExtension::None,
            inreg: false,
            audited,
            newtype: false,
        };
        fx.items[0].state = WorkState::Admitted { abi: abi(vec![float], direct(64)) };
        let out = fx.run();
        refused_with(&out, RefusalClass::UnsupportedAbi, "_RFadd", "argument 0");
        assert!(names(&out).is_empty(), "a float signature is refused, never compiled Unknown");
    }
}

// ---- rule 1: the handoff closure in `star` --------------------------------------------------

/// Rule 1: when `star` was built, every body in a HANDOFF item's closure must be equal in
/// `base` and `star`. Without the rule (MEASURED, INC5.4-FREEZE) the relinked closure ships.
#[test]
fn handoff_body_that_differs_in_star_refuses() {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let f = fx.body("crate::f", &[g]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    fx.items[0].handoff = true;
    fx.items[1].handoff = true;
    fx.base = Some(fx.m.clone());
    clean(&fx.run());
    // `star` relinked g's body: g now calls itself.
    let edited = fx.function_mut(g);
    edited.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(1) })
            .with_result(ValueId::new(9)),
    );
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "differs between");
    assert!(!names(&out).contains(&"_RF"));
}

#[test]
fn handoff_declaration_replacement_without_installation_custody_refuses() {
    let mut fx = Fixture::new();
    let g = fx.decl("crate::g");
    let f = fx.body("crate::f", &[g]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    fx.items[0].handoff = true;
    fx.base = Some(fx.m.clone());
    let temporary = fx.body("crate::temporary", &[]);
    let mut replacement = fx.m.functions.pop().unwrap();
    assert_eq!(replacement.id, temporary);
    replacement.id = g;
    replacement.name = "crate::g".into();
    *fx.function_mut(g) = replacement;
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "no retained authenticated");
    assert!(!names(&out).contains(&"_RF"));
}

#[test]
fn postcondition_rederives_handoff_declaration_installation_custody() {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let f = fx.body("crate::f", &[g]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    let assembled = assemble(&fx.input());
    assert!(assembled.output.refusals.is_empty());
    assert!(check_postcondition(&fx.input(), &assembled).is_empty());
    // Keep the produced M_cg untouched but supply a handoff original in which
    // g was a declaration. Assembly's old success cannot authorize this input.
    fx.items[0].handoff = true;
    let mut base = fx.m.clone();
    base.functions[g.as_usize()].blocks.clear();
    fx.base = Some(base);
    let errors = check_postcondition(&fx.input(), &assembled);
    assert!(errors.iter().any(|error| error.to_string().contains(
        "no retained authenticated declaration extension")), "{errors:?}");
}

// ---- dropping callers -----------------------------------------------------------------------

/// A caller of a refused item (and its caller) is refused and dropped; the rest of the
/// admitted subset stays in M_cg for trust-cg's census.
#[test]
fn a_caller_of_a_refused_item_is_refused_and_dropped_from_m_cg() {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let f = fx.body("crate::f", &[g]);
    let e = fx.body("crate::e", &[f]);
    let lone = fx.body("crate::lone", &[]);
    fx.item("_RE", e);
    fx.item("_RF", f);
    fx.item("_RG", g);
    fx.item("_RLone", lone);
    fx.items[2].state = WorkState::Refused;
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "_RF", "calls `_RG`, which is refused");
    refused_with(&out, RefusalClass::CodegenModule, "_RE", "calls `_RF`, which is refused");
    assert_eq!(names(&out), ["_RLone"], "only the independent body stays");
}

// ---- rule 5: function references ------------------------------------------------------------

fn with_const(value: Constant) -> CodegenModuleOutput {
    let mut fx = Fixture::new();
    let g = fx.body("crate::g", &[]);
    let f = fx.body("crate::f", &[]);
    let _ = g;
    fx.m.globals.push(global(
        "__trust_promoted_0",
        Linkage::Internal,
        false,
        Some(Constant::Int(0)),
    ));
    fx.function_mut(f).blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::Const { ty: Ty::Ptr, value }).with_result(ValueId::new(7)));
    fx.item("_RF", f);
    fx.run()
}

/// INC5.4-FNREF: `FnDef`, `Closure` and function-naming `SymbolAddr` constants refuse, in a
/// body and in a global initializer; a `SymbolAddr` naming a global does not.
#[test]
fn fn_def_closure_and_symbol_addr_constants_refuse() {
    for value in [
        Constant::FnDef(FuncId::new(0)),
        Constant::Closure { func: FuncId::new(0), captures: vec![] },
        Constant::SymbolAddr { symbol: "crate::g".into(), addend: 0 },
        Constant::SymbolAddr { symbol: "nowhere".into(), addend: 0 },
    ] {
        let out = with_const(value.clone());
        refused_with(&out, RefusalClass::CodegenModule, "_RF", "INC5.4-FNREF");
        assert!(names(&out).is_empty(), "{value:?}");
    }
    let mut fx = Fixture::new();
    fx.m.globals.push(global(
        "__trust_promoted_0",
        Linkage::Internal,
        false,
        Some(Constant::Int(0)),
    ));
    let to_global = Constant::SymbolAddr { symbol: "__trust_promoted_0".into(), addend: 0 };
    assert_eq!(constant_reference(&fx.m, &to_global), None, "a global's address is data");
    let _ = fx.body("crate::f", &[]);

    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    fx.m.globals.push(global(
        "__trust_promoted_1",
        Linkage::Internal,
        false,
        Some(Constant::FnDef(f)),
    ));
    refused_with(&fx.run(), RefusalClass::CodegenModule, "__trust_promoted_1", "pointer-bearing");
}

/// INC5.4-FNREF: indirect, invoke and `SeqMap` sites refuse.
#[test]
fn indirect_invoke_and_seqmap_sites_refuse() {
    let sites = |f: FuncId, sig: FuncTyId| -> Vec<Inst> {
        vec![
            Inst::CallIndirect {
                callee: ValueId::new(0),
                sig,
                args: vec![],
                calling_conv: trust_ir::CallingConv::Rust,
            },
            Inst::Invoke {
                callee: f,
                args: vec![],
                normal_dest: BlockId::new(0),
                normal_args: vec![],
                unwind_dest: BlockId::new(0),
            },
            Inst::SeqMap { ty: Ty::U64, seq: ValueId::new(0), fwd: f },
        ]
    };
    let probe = Fixture::new();
    for inst in sites(FuncId::new(0), probe.sig) {
        let mut fx = Fixture::new();
        let f = fx.body("crate::f", &[]);
        fx.function_mut(f).blocks[0].body.insert(0, InstrNode::new(inst.clone()));
        fx.item("_RF", f);
        let out = fx.run();
        refused_with(&out, RefusalClass::CodegenModule, "_RF", "INC5.4-FNREF");
        assert!(names(&out).is_empty(), "{inst:?}");
    }
}

/// INC5.4-FNREF: a non-empty drop-glue table refuses.
#[test]
fn non_empty_drop_glue_table_refuses() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    clean(&fx.run());
    fx.m.drop_glue.push(DropGlueEntry { glue: f, ty: Ty::U64 });
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "k", "drop-glue table");
    assert!(out.m_cg.drop_glue.is_empty(), "M_cg never carries the stale table");
}

/// Trust: trust-ir v70: a non-empty tensor weight-blob table refuses the module by name, and
/// M_cg carries the producer's table verbatim rather than dropping the bytes its constants name.
#[test]
fn non_empty_blob_table_refuses() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    clean(&fx.run());
    fx.m.intern_blob(vec![0, 0, 0, 0]);
    let out = fx.run();
    refused_with(&out, RefusalClass::CodegenModule, "k", "tensor weight-blob table");
    assert_eq!(out.m_cg.blobs, fx.m.blobs, "M_cg carries the table, never drops it");
}

/// INC5.4-FNREF: a function-symbol proxy global refuses.
#[test]
fn function_symbol_proxy_global_refuses() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    let mut proxy = global("crate::f", Linkage::External, false, None);
    proxy.ty = Ty::Ptr;
    fx.m.globals.push(proxy);
    refused_with(&fx.run(), RefusalClass::CodegenModule, "crate::f", "proxy");
}

/// INC5.4-FNREF: M_cg carries no proof obligations, certificates, obligation diagnostics,
/// spec modules or summaries; the PRODUCER keeps them (the gate reads it). Without the strip
/// (MEASURED, INC5.4-FREEZE) M_cg carries the producer's stale tables.
#[test]
fn proof_tables_and_summaries_are_stripped_from_m_cg_only() {
    let mut fx = Fixture::new();
    let f = fx.body("crate::f", &[]);
    fx.item("_RF", f);
    fx.function_mut(f).summary = Some(FunctionSummary::default());
    fx.m.proof_obligations.push(
        ProofObligation::new(
            trust_ir::value::ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "f's postcondition",
        )
        .with_function(f),
    );
    let out = fx.run();
    clean(&out);
    assert!(out.m_cg.proof_obligations.is_empty(), "M_cg carries the stale obligation table");
    assert!(out.m_cg.proof_certificates.is_empty());
    assert!(out.m_cg.obligation_diagnostics.is_empty());
    assert!(out.m_cg.spec_modules.is_empty());
    assert!(find(&out, "_RF").summary.is_none(), "M_cg carries the stale summary");
    // The producer is untouched.
    assert_eq!(fx.m.proof_obligations.len(), 1);
    assert!(fx.m.function_by_id(f).unwrap().summary.is_some());
}

/// Rule 11: `#[inline(never)]` items (and residue) form the never-inline set.
#[test]
fn never_inline_set_is_rustcs() {
    let mut fx = Fixture::new();
    let h = fx.body("crate::h", &[]);
    let g = fx.body("crate::g", &[]);
    let f = fx.body("crate::f", &[g, h]);
    fx.item("_RF", f);
    fx.item("_RG", g);
    fx.items[1].never_inline = true;
    fx.residue.insert(
        h,
        ResidueIdentity::Local { symbol: "_RH".into(), abi: u64_abi(), never_inline: true },
    );
    let out = fx.run();
    clean(&out);
    assert_eq!(out.never_inline, BTreeSet::from(["_RG".to_string(), "_RH".to_string()]));
}

// ---- rule 9 (5.4.3): legalization from rustc's FnAbi ----------------------------------------

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

/// A node defining value `result`.
fn def(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}

fn ret(values: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Return { values: values.iter().copied().map(v).collect() })
}

fn scalar(bits: u32, kind: ScalarKind) -> ScalarShape {
    ScalarShape { bits, kind, ext: AbiExtension::None, inreg: false }
}

const INT: ScalarKind = ScalarKind::Int { signed: false };

fn pair(first: ScalarShape, second: ScalarShape, of: PairOf) -> ArgShape {
    ArgShape::Pair { first, second, of, audited: true }
}

fn indirect() -> ArgShape {
    ArgShape::Indirect { on_stack: false, has_meta: false, audited: true }
}

impl Fixture {
    /// `name(params..) -> returns` whose one block is `nodes`; parameter `i` is value `i`.
    fn func(
        &mut self,
        name: &str,
        params: Vec<Ty>,
        returns: Vec<Ty>,
        nodes: Vec<InstrNode>,
    ) -> FuncId {
        let sig = self
            .m
            .intern_func_type(FuncTy {
                params: params.clone(),
                returns,
                is_vararg: false,
                abi: None,
            })
            .expect("Module::intern_func_type: test fixture");
        let id = FuncId::new(self.m.functions.len() as u32);
        let mut f = Function::new(id, name, sig, BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        for (i, ty) in params.iter().enumerate() {
            b = b.with_param(v(i as u32), ty.clone());
        }
        b.body = nodes;
        f.blocks.push(b);
        f.producer = Some(Producer::TRust);
        f.body_gate = Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
        self.m.try_add_function(f).expect("Module::try_add_function: test fixture");
        id
    }

    /// A bodyless `name(params..) -> returns` declaration.
    fn decl_sig(&mut self, name: &str, params: Vec<Ty>, returns: Vec<Ty>) -> FuncId {
        let sig = self
            .m
            .intern_func_type(FuncTy { params, returns, is_vararg: false, abi: None })
            .expect("Module::intern_func_type: test fixture");
        let id = FuncId::new(self.m.functions.len() as u32);
        let mut f = Function::new(id, name, sig, BlockId::new(0));
        f.producer = Some(Producer::TRust);
        self.m.try_add_function(f).expect("Module::try_add_function: test fixture");
        id
    }

    fn item_abi(&mut self, symbol: &str, func: FuncId, abi: AbiShape) {
        self.item(symbol, func);
        self.items.last_mut().unwrap().state = WorkState::Admitted { abi };
    }

    /// A struct with recorded offsets and size; field `i` is named `f{i}`.
    fn struct_ty(&mut self, name: &str, fields: &[(Ty, u64)], size: u64) -> Ty {
        let id = StructId::new(self.m.structs.len() as u32);
        self.m.add_struct(StructDef {
            id,
            name: name.to_string(),
            fields: fields
                .iter()
                .enumerate()
                .map(|(i, (ty, offset))| FieldDef {
                    name: format!("f{i}"),
                    ty: ty.clone(),
                    offset: Some(*offset),
                })
                .collect(),
            size: Some(size),
            align: Some(8),
            repr: StructRepr::Rust,
            origin: None,
        });
        Ty::Struct(id)
    }

    /// `&[u8]`.
    fn slice_ty(&mut self) -> Ty {
        let elem = self.m.add_type(Ty::U8).expect("Module::add_type: test fixture");
        Ty::FatPtr(FatPtrKind::Slice(elem))
    }
}

fn signature<'a>(out: &'a CodegenModuleOutput, symbol: &str) -> &'a FuncTy {
    &out.m_cg.func_types[find(out, symbol).ty.as_usize()]
}

fn entry(f: &Function) -> &Block {
    f.blocks.iter().find(|b| b.id == f.entry).expect("an entry block")
}

/// The legalization fixture of `pair_indirect_sret_are_legalized_per_fnabi`: one function per
/// 5.4.3 shape, and a caller of each.
///
/// * `S2 { f0: u32 @ 8, f1: u64 @ 0 }`: a `repr(Rust)`-reordered pair, so rustc's half 0 (the
///   scalar at offset 0) is field 1.
/// * `S24 { u64, u64, u64 }`: passed and returned indirectly.
fn legalization_fixture() -> (Fixture, Ty, Ty, Ty, Ty) {
    let mut fx = Fixture::new();
    let s2 = fx.struct_ty("S2", &[(Ty::U32, 8), (Ty::U64, 0)], 16);
    let s24 = fx.struct_ty("S24", &[(Ty::U64, 0), (Ty::U64, 8), (Ty::U64, 16)], 24);
    let tup = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let slice = fx.slice_ty();
    let pair_s2 = fx.func(
        "crate::pair_s2",
        vec![s2.clone()],
        vec![Ty::U64],
        vec![def(Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 1 }, 1), ret(&[1])],
    );
    let pair_tuple =
        fx.func("crate::pair_tuple", vec![tup.clone()], vec![tup.clone()], vec![ret(&[0])]);
    let slice_len = fx.func(
        "crate::slice_len",
        vec![slice.clone()],
        vec![Ty::U64],
        vec![
            def(Inst::PtrMetadata { ptr_ty: slice.clone(), metadata_ty: Ty::U64, ptr: v(0) }, 1),
            ret(&[1]),
        ],
    );
    let slice_fwd = fx.func(
        "crate::slice_fwd",
        vec![slice.clone()],
        vec![Ty::U64],
        vec![def(Inst::Call { callee: slice_len, args: vec![v(0)] }, 1), ret(&[1])],
    );
    let by_ref = fx.func(
        "crate::by_ref",
        vec![s24.clone()],
        vec![Ty::U64],
        vec![def(Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 2 }, 1), ret(&[1])],
    );
    let make24 = fx.func(
        "crate::make24",
        vec![Ty::U64],
        vec![s24.clone()],
        vec![
            def(Inst::MakeAggregate { ty: s24.clone(), variant: None, fields: vec![v(0); 3] }, 1),
            ret(&[1]),
        ],
    );
    let caller = fx.func(
        "crate::caller",
        vec![Ty::U64],
        vec![Ty::U64],
        vec![
            def(Inst::Call { callee: make24, args: vec![v(0)] }, 1),
            def(Inst::Call { callee: by_ref, args: vec![v(1)] }, 2),
            def(
                Inst::MakeAggregate { ty: tup.clone(), variant: None, fields: vec![v(2), v(0)] },
                3,
            ),
            def(Inst::Call { callee: pair_tuple, args: vec![v(3)] }, 4),
            def(Inst::ExtractField { ty: Ty::U64, aggregate: v(4), field: 0 }, 5),
            def(Inst::Const { ty: Ty::U32, value: Constant::Int(7) }, 6),
            def(Inst::MakeAggregate { ty: s2.clone(), variant: None, fields: vec![v(6), v(5)] }, 7),
            def(Inst::Call { callee: pair_s2, args: vec![v(7)] }, 8),
            ret(&[8]),
        ],
    );
    let s2_pair = pair(scalar(64, INT), scalar(32, INT), PairOf::Fields([1, 0]));
    let tuple_pair = pair(scalar(64, INT), scalar(64, INT), PairOf::Fields([0, 1]));
    let slice_pair = pair(scalar(64, ScalarKind::Pointer), scalar(64, INT), PairOf::SliceRef);
    fx.item_abi("_RCaller", caller, u64_abi());
    fx.item_abi("_RPairS2", pair_s2, abi(vec![s2_pair], direct(64)));
    fx.item_abi("_RPairTuple", pair_tuple, abi(vec![tuple_pair.clone()], tuple_pair));
    fx.item_abi("_RSliceLen", slice_len, abi(vec![slice_pair.clone()], direct(64)));
    fx.item_abi("_RSliceFwd", slice_fwd, abi(vec![slice_pair], direct(64)));
    fx.item_abi("_RByRef", by_ref, abi(vec![indirect()], direct(64)));
    fx.item_abi("_RMake24", make24, abi(vec![direct(64)], indirect()));
    (fx, s2, s24, tup, slice)
}

/// Rule 9 (5.4.3) and rule 10: each shape is legalized EXACTLY as rustc's FnAbi passes it —
/// a reordered struct pair in LAYOUT order (half 0 is field 1), a tuple pair and a pair result,
/// a slice reference as (data, length), a by-value struct through a pointer the caller fills,
/// an sret result through a leading `ParamAttrs.sret` pointer — at the definition's entry and
/// returns and at every call site, with P read from the FnAbi. Then the postcondition's teeth:
/// a pair's halves swapped between `assemble` and `check_postcondition` (at an entry rebuild
/// and at a call site), and an sret store or load dropped, are each refused.
#[test]
fn pair_indirect_sret_are_legalized_per_fnabi() {
    let (fx, s2, s24, tup, slice) = legalization_fixture();
    let out = fx.run();
    clean(&out);

    // -- the reordered struct pair: (u64, u32), rebuilt with field 0 <- half 1, field 1 <- half 0.
    assert_eq!(signature(&out, "_RPairS2").params, vec![Ty::U64, Ty::U32]);
    let f = find(&out, "_RPairS2");
    assert_eq!(entry(f).params, vec![(v(2), Ty::U64), (v(3), Ty::U32)]);
    assert_eq!(
        entry(f).body[0].inst,
        Inst::MakeAggregate { ty: s2.clone(), variant: None, fields: vec![v(3), v(2)] }
    );
    assert_eq!(entry(f).body[0].results, vec![v(0)]);
    assert_eq!(
        out.placements["_RPairS2"].params,
        vec![ParamPlace::Pair(ScalarPlace::gpr(1, 32), ScalarPlace::gpr(0, 64))],
        "P is per field: field 0 rides X1, field 1 X0"
    );

    // -- the tuple pair, argument and result: no P (P has no Pair result).
    let t = signature(&out, "_RPairTuple");
    assert_eq!((t.params.clone(), t.returns.clone()), (vec![Ty::U64; 2], vec![Ty::U64; 2]));
    let f = find(&out, "_RPairTuple");
    assert_eq!(
        entry(f).body[0].inst,
        Inst::MakeAggregate { ty: tup.clone(), variant: None, fields: vec![v(1), v(2)] }
    );
    assert_eq!(
        entry(f).body[1..].iter().map(|n| n.inst.clone()).collect::<Vec<_>>(),
        vec![
            Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 0 },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 1 },
            Inst::Return { values: vec![v(3), v(4)] },
        ]
    );
    assert!(!out.placements.contains_key("_RPairTuple"), "a Pair result has no P: Unknown");

    // -- the slice reference: (data, length), rebuilt with `PtrFromParts`.
    assert_eq!(signature(&out, "_RSliceLen").params, vec![Ty::Ptr, Ty::U64]);
    assert_eq!(
        entry(find(&out, "_RSliceLen")).body[0].inst,
        Inst::PtrFromParts {
            ptr_ty: slice.clone(),
            metadata_ty: Ty::U64,
            data: v(2),
            metadata: v(3),
        }
    );
    assert_eq!(
        out.placements["_RSliceLen"].params,
        vec![ParamPlace::Pair(ScalarPlace::gpr(0, 64), ScalarPlace::gpr(1, 64))]
    );
    // ... and split with `PtrData`/`PtrMetadata` where it is passed on.
    let fwd = &entry(find(&out, "_RSliceFwd")).body;
    assert_eq!(fwd[1].inst, Inst::PtrData { ptr_ty: slice.clone(), ptr: v(0) });
    assert_eq!(
        fwd[2].inst,
        Inst::PtrMetadata { ptr_ty: slice.clone(), metadata_ty: Ty::U64, ptr: v(0) }
    );
    assert!(
        matches!(&fwd[3].inst, Inst::Call { args, .. } if *args == fwd[1].results.iter().chain(&fwd[2].results).copied().collect::<Vec<_>>())
    );

    // -- the by-value struct: a pointer parameter and a `Load` at entry; P `Slot::Indirect`.
    assert_eq!(signature(&out, "_RByRef").params, vec![Ty::Ptr]);
    assert_eq!(
        entry(find(&out, "_RByRef")).body[0].inst,
        Inst::Load { ty: s24.clone(), ptr: v(2), volatile: false, align: None }
    );
    assert_eq!(
        out.placements["_RByRef"].params,
        vec![ParamPlace::Scalar(ScalarPlace {
            slot: Slot::Indirect,
            width: 64,
            ext: AbiExt::None
        })]
    );

    // -- the sret result: a leading `sret` pointer, no result, a `Store` at the `Return`.
    let t = signature(&out, "_RMake24");
    assert_eq!((t.params.clone(), t.returns.clone()), (vec![Ty::Ptr, Ty::U64], vec![]));
    let f = find(&out, "_RMake24");
    assert_eq!(f.attrs.params, vec![ParamAttrs { sret: true, ..ParamAttrs::default() }]);
    assert_eq!(entry(f).params, vec![(v(2), Ty::Ptr), (v(0), Ty::U64)]);
    let tail: Vec<Inst> = entry(f).body[1..].iter().map(|n| n.inst.clone()).collect();
    assert_eq!(
        tail,
        vec![
            Inst::Store { ty: s24.clone(), ptr: v(2), value: v(1), volatile: false, align: None },
            Inst::Return { values: vec![] },
        ]
    );
    assert_eq!(out.placements["_RMake24"].ret, ReturnPlace::Indirect);
    assert_eq!(
        out.placements["_RMake24"].params,
        vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))]
    );

    // -- the caller: an identity signature whose every call site is legalized.
    let caller = find(&out, "_RCaller");
    assert_eq!(caller.ty, fx.m.function_by_id(FuncId::new(6)).unwrap().ty, "own plan: identity");
    let insts: Vec<Inst> = entry(caller).body.iter().map(|n| n.inst.clone()).collect();
    let make24 = find(&out, "_RMake24").id;
    let by_ref = find(&out, "_RByRef").id;
    let pair_tuple = find(&out, "_RPairTuple").id;
    let pair_s2 = find(&out, "_RPairS2").id;
    assert_eq!(
        insts,
        vec![
            // The hoisted caller-frame slots: make24's sret buffer, then by_ref's copy.
            Inst::Alloca { ty: s24.clone(), count: None, align: None },
            Inst::Alloca { ty: s24.clone(), count: None, align: None },
            Inst::Call { callee: make24, args: vec![v(9), v(0)] },
            Inst::Load { ty: s24.clone(), ptr: v(9), volatile: false, align: None },
            Inst::Store { ty: s24.clone(), ptr: v(10), value: v(1), volatile: false, align: None },
            Inst::Call { callee: by_ref, args: vec![v(10)] },
            Inst::MakeAggregate { ty: tup.clone(), variant: None, fields: vec![v(2), v(0)] },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(3), field: 0 },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(3), field: 1 },
            Inst::Call { callee: pair_tuple, args: vec![v(11), v(12)] },
            Inst::MakeAggregate { ty: tup.clone(), variant: None, fields: vec![v(13), v(14)] },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(4), field: 0 },
            Inst::Const { ty: Ty::U32, value: Constant::Int(7) },
            Inst::MakeAggregate { ty: s2.clone(), variant: None, fields: vec![v(6), v(5)] },
            // Half 0 is field 1 (the u64), half 1 field 0 (the u32).
            Inst::ExtractField { ty: Ty::U64, aggregate: v(7), field: 1 },
            Inst::ExtractField { ty: Ty::U32, aggregate: v(7), field: 0 },
            Inst::Call { callee: pair_s2, args: vec![v(15), v(16)] },
            Inst::Return { values: vec![v(8)] },
        ]
    );
    // The producer bodies the gate reads are untouched.
    assert_eq!(fx.m.function_by_id(FuncId::new(6)).unwrap().blocks[0].body.len(), 9);

    // -- the postcondition's teeth: each mutation BETWEEN `assemble` and `check_postcondition`.
    let input = fx.input();
    let mutated = |symbol: &str, edit: &dyn Fn(&mut Vec<InstrNode>)| -> Vec<String> {
        let mut assembled = assemble(&input);
        assert!(check_postcondition(&input, &assembled).is_empty(), "unmutated: clean");
        let f = assembled.output.m_cg.functions.iter_mut().find(|f| f.name == symbol).unwrap();
        let entry_id = f.entry;
        edit(&mut f.blocks.iter_mut().find(|b| b.id == entry_id).unwrap().body);
        check_postcondition(&input, &assembled).iter().map(|r| r.to_string()).collect()
    };
    let refused = |post: Vec<String>, what: &str| {
        assert!(
            post.iter().any(|r| r.contains("differs from its producer body")
                && r.contains("rule 9's legalization")),
            "{what} must be refused: {post:?}"
        );
    };
    // (a) the entry rebuild's halves swapped (the producer's field order instead of rustc's).
    refused(
        mutated("_RPairS2", &|body| {
            let Inst::MakeAggregate { fields, .. } = &mut body[0].inst else { panic!() };
            fields.swap(0, 1);
        }),
        "an entry rebuild with swapped halves",
    );
    // (b) a call site's halves swapped: field 0 first.
    refused(
        mutated("_RCaller", &|body| {
            let (a, b) = (body[14].inst.clone(), body[15].inst.clone());
            body[14].inst = b;
            body[15].inst = a;
        }),
        "a call site with swapped halves",
    );
    // (c) the sret store dropped before the `Return`.
    refused(
        mutated("_RMake24", &|body| {
            body.remove(1);
        }),
        "an sret result whose store is dropped",
    );
    // (d) the load after an sret call dropped.
    refused(
        mutated("_RCaller", &|body| {
            body.remove(3);
        }),
        "an sret call whose load is dropped",
    );
    // (e) one slot shared by two call sites.
    refused(
        mutated("_RCaller", &|body| {
            let Inst::Store { ptr, .. } = &mut body[4].inst else { panic!() };
            *ptr = v(9);
        }),
        "a caller-frame slot shared by two sites",
    );
}

/// Rule 9's cross-checks: a struct pair whose recorded offsets disagree with rustc's halves, a
/// pair enum (INC5.4-PAIR-ENUM), an unaudited pair (`&mut [T]`), a pair whose lanes are not
/// scalars, an `Indirect` struct without a recorded layout, a newtype rustc does not mark, and
/// an entry block an edge re-enters all refuse `[unsupported-abi]`.
#[test]
fn legalization_refuses_what_it_cannot_cross_check() {
    let pair_fn = |fx: &mut Fixture, ty: Ty| {
        fx.func(
            "crate::f",
            vec![ty],
            vec![Ty::U64],
            vec![def(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }, 1), ret(&[1])],
        )
    };
    // Offsets that put half 0's field at 8.
    let mut fx = Fixture::new();
    let s2 = fx.struct_ty("S2", &[(Ty::U32, 8), (Ty::U64, 0)], 16);
    let f = pair_fn(&mut fx, s2);
    fx.item_abi(
        "_RF",
        f,
        abi(vec![pair(scalar(64, INT), scalar(32, INT), PairOf::Fields([0, 1]))], direct(64)),
    );
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "half 0 (field 0)");
    let mut fx = Fixture::new();
    let s2 = fx.struct_ty("S2", &[(Ty::U64, 8), (Ty::U64, 0)], 16);
    let f = pair_fn(&mut fx, s2);
    fx.item_abi(
        "_RF",
        f,
        abi(vec![pair(scalar(64, INT), scalar(64, INT), PairOf::Fields([0, 1]))], direct(64)),
    );
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "rustc's pair puts them at 0");

    // A pair enum: refused by name, never rebuilt.
    let mut fx = Fixture::new();
    let f = pair_fn(&mut fx, Ty::Enum(trust_ir::EnumId::new(0)));
    fx.item_abi(
        "_RF",
        f,
        abi(vec![pair(scalar(64, INT), scalar(64, INT), PairOf::Enum)], direct(64)),
    );
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "INC5.4-PAIR-ENUM");

    // `&mut [u8]` (rustc's slice pair, unaudited).
    let mut fx = Fixture::new();
    let slice = fx.slice_ty();
    let f = pair_fn(&mut fx, slice);
    let mut shape = pair(scalar(64, ScalarKind::Pointer), scalar(64, INT), PairOf::SliceRef);
    let ArgShape::Pair { audited, .. } = &mut shape else { panic!() };
    *audited = false;
    fx.item_abi("_RF", f, abi(vec![shape], direct(64)));
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "outside the audited pairs");

    // A pair of a struct whose lanes are structs.
    let mut fx = Fixture::new();
    let inner = fx.struct_ty("W", &[(Ty::U64, 0)], 8);
    let outer = fx.struct_ty("P", &[(inner.clone(), 0), (inner, 8)], 16);
    let f = pair_fn(&mut fx, outer);
    fx.item_abi(
        "_RF",
        f,
        abi(vec![pair(scalar(64, INT), scalar(64, INT), PairOf::Fields([0, 1]))], direct(64)),
    );
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "is not an integer");

    // An indirect struct with no recorded offsets.
    let mut fx = Fixture::new();
    let s24 = fx.struct_ty("S24", &[(Ty::U64, 0), (Ty::U64, 8), (Ty::U64, 16)], 24);
    let Ty::Struct(id) = s24 else { panic!() };
    fx.m.structs.iter_mut().find(|s| s.id == id).unwrap().fields[1].offset = None;
    let f = pair_fn(&mut fx, s24);
    fx.item_abi("_RF", f, abi(vec![indirect()], direct(64)));
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "no complete layout");

    // A newtype: admitted when rustc marks it, refused when it does not.
    let mut fx = Fixture::new();
    let w = fx.struct_ty("W", &[(Ty::U64, 0)], 8);
    let f = fx.func("crate::f", vec![w.clone()], vec![w.clone()], vec![ret(&[0])]);
    let newtype = ArgShape::Direct {
        bits: 64,
        kind: INT,
        ext: AbiExtension::None,
        inreg: false,
        audited: false,
        newtype: true,
    };
    fx.item_abi("_RF", f, abi(vec![newtype.clone()], newtype.clone()));
    let out = fx.run();
    clean(&out);
    let t = signature(&out, "_RF");
    assert_eq!((t.params.clone(), t.returns.clone()), (vec![Ty::U64], vec![Ty::U64]));
    let body: Vec<Inst> = entry(find(&out, "_RF")).body.iter().map(|n| n.inst.clone()).collect();
    assert_eq!(
        body,
        vec![
            Inst::MakeAggregate { ty: w.clone(), variant: None, fields: vec![v(1)] },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 0 },
            Inst::Return { values: vec![v(2)] },
        ]
    );
    assert_eq!(out.placements["_RF"].params, vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))]);
    let unmarked = ArgShape::Direct {
        bits: 64,
        kind: INT,
        ext: AbiExtension::None,
        inreg: false,
        audited: false,
        newtype: false,
    };
    fx.items[0].state = WorkState::Admitted { abi: abi(vec![unmarked], newtype) };
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "does not mark as a newtype");

    // An entry block an edge re-enters: its rebuild would run again on that edge.
    let mut fx = Fixture::new();
    let w = fx.struct_ty("W", &[(Ty::U64, 0)], 8);
    let f = fx.func(
        "crate::f",
        vec![w.clone()],
        vec![Ty::U64],
        vec![InstrNode::new(Inst::Br { target: BlockId::new(0), args: vec![v(0)] })],
    );
    let newtype = ArgShape::Direct {
        bits: 64,
        kind: INT,
        ext: AbiExtension::None,
        inreg: false,
        audited: false,
        newtype: true,
    };
    fx.item_abi("_RF", f, abi(vec![newtype], direct(64)));
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RF", "re-enters the entry block");

    // Per-parameter attributes a legalized signature would have to re-place.
    let (mut fx, ..) = legalization_fixture();
    let by_ref = fx.m.functions.iter().find(|f| f.name == "crate::by_ref").unwrap().id;
    fx.function_mut(by_ref).attrs.params =
        vec![ParamAttrs { nonnull: true, ..ParamAttrs::default() }];
    refused_with(&fx.run(), RefusalClass::UnsupportedAbi, "_RByRef", "per-parameter attributes");
}

/// Rule 9 (5.4.3): an `Ignore` (zero-sized) argument is dropped at BOTH ends — from the
/// definition's signature and entry block, and from every call site's arguments — and P places
/// it `ParamPlace::Ignore`. A body that READS the dropped value is refused (nothing rebuilds
/// it), and an `Ignore` slot over a non-zero-sized producer type is a mismatch.
#[test]
fn ignore_arg_is_dropped_at_both_ends() {
    let build = |reads: bool| {
        let mut fx = Fixture::new();
        let sink = fx.func("crate::sink", vec![Ty::Unit], vec![], vec![ret(&[])]);
        let mut body = vec![];
        if reads {
            body.push(InstrNode::new(Inst::Call { callee: sink, args: vec![v(1)] }));
        }
        body.push(ret(&[0]));
        let f = fx.func("crate::f", vec![Ty::U64, Ty::Unit], vec![Ty::U64], body);
        fx.function_mut(f).value_names = Some(vec![(v(0), "x".into()), (v(1), "_m".into())]);
        let g = fx.func(
            "crate::g",
            vec![Ty::U64],
            vec![Ty::U64],
            vec![
                def(Inst::Const { ty: Ty::Unit, value: Constant::PhantomData }, 1),
                def(Inst::Call { callee: f, args: vec![v(0), v(1)] }, 2),
                ret(&[2]),
            ],
        );
        fx.item_abi("_RG", g, u64_abi());
        fx.item_abi("_RF", f, abi(vec![direct(64), ArgShape::Ignore], direct(64)));
        fx.item_abi("_RSink", sink, abi(vec![ArgShape::Ignore], ArgShape::Ignore));
        fx
    };
    let fx = build(false);
    let out = fx.run();
    clean(&out);
    assert_eq!(signature(&out, "_RF").params, vec![Ty::U64], "dropped from the signature");
    assert_eq!(entry(find(&out, "_RF")).params, vec![(v(0), Ty::U64)], "and from the entry");
    assert_eq!(
        entry(find(&out, "_RF")).body,
        fx.m.function_by_id(FuncId::new(1)).unwrap().blocks[0].body,
        "no rebuild"
    );
    assert_eq!(
        find(&out, "_RF").value_names,
        Some(vec![(v(0), "x".to_string())]),
        "the dropped argument's debug name goes with it (validate_module refuses a dangling one)"
    );
    let f_id = find(&out, "_RF").id;
    assert_eq!(
        entry(find(&out, "_RG")).body[1].inst,
        Inst::Call { callee: f_id, args: vec![v(0)] },
        "and from the call site"
    );
    assert_eq!(
        out.placements["_RF"].params,
        vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64)), ParamPlace::Ignore]
    );

    let out = build(true).run();
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "is read by the body");
    refused_with(&out, RefusalClass::CodegenModule, "_RG", "calls `_RF`, which is refused");

    // rustc passes nothing, the producer passes a `u64`: a mismatch, never a dropped value.
    let out = single(&mut Fixture::new(), abi(vec![ArgShape::Ignore], direct(64)));
    refused_with(&out, RefusalClass::UnsupportedAbi, "_RF", "is not zero-sized");
}

/// Rule 3 with rule 9 (INC5.4-5.6-HOOKS, critique L7): a call site to a DECLARATION is legalized
/// as a call to a body is, and the declaration is signed with its FnAbi-legalized signature, so
/// 5.6 needs no edit here. DORMANT: the plugin's `declarations` map is empty until 5.6.3, and
/// then admits only an allow-list of shapes (INC5.6-DECL-SHAPES), so with the map empty the same
/// module refuses. The comparison tells a genuine mismatch from an outside-the-subset shape
/// (5.6.1(b) maps them to different classes).
#[test]
fn declaration_call_sites_are_legalized_dormant() {
    let build = || {
        let mut fx = Fixture::new();
        let s24 = fx.struct_ty("S24", &[(Ty::U64, 0), (Ty::U64, 8), (Ty::U64, 16)], 24);
        let tup = Ty::Tuple(vec![Ty::U64, Ty::U64]);
        let ext_pair = fx.decl_sig("ext_pair", vec![tup.clone()], vec![Ty::U64]);
        let ext_make = fx.decl_sig("ext_make", vec![Ty::U64], vec![s24.clone()]);
        let f = fx.func(
            "crate::f",
            vec![Ty::U64],
            vec![Ty::U64],
            vec![
                def(
                    Inst::MakeAggregate {
                        ty: tup.clone(),
                        variant: None,
                        fields: vec![v(0), v(0)],
                    },
                    1,
                ),
                def(Inst::Call { callee: ext_pair, args: vec![v(1)] }, 2),
                def(Inst::Call { callee: ext_make, args: vec![v(2)] }, 3),
                def(Inst::ExtractField { ty: Ty::U64, aggregate: v(3), field: 1 }, 4),
                ret(&[4]),
            ],
        );
        fx.item("_RF", f);
        (fx, s24, tup)
    };
    // Dormant: with the production map (empty until 5.6.3) every declaration refuses.
    let (fx, ..) = build();
    refused_with(&fx.run(), RefusalClass::CodegenModule, "_RF", "carries no link symbol");

    // With the 5.6 shape of the map, the declarations are signed legalized and the call sites
    // legalized.
    let (mut fx, s24, tup) = build();
    let tuple_pair = pair(scalar(64, INT), scalar(64, INT), PairOf::Fields([0, 1]));
    fx.declarations.insert("ext_pair".into(), abi(vec![tuple_pair], direct(64)));
    fx.declarations.insert("ext_make".into(), abi(vec![direct(64)], indirect()));
    let out = fx.run();
    clean(&out);
    let t = signature(&out, "ext_pair");
    assert_eq!((t.params.clone(), t.returns.clone()), (vec![Ty::U64, Ty::U64], vec![Ty::U64]));
    let t = signature(&out, "ext_make");
    assert_eq!((t.params.clone(), t.returns.clone()), (vec![Ty::Ptr, Ty::U64], vec![]));
    assert_eq!(
        find(&out, "ext_make").attrs.params,
        vec![ParamAttrs { sret: true, ..ParamAttrs::default() }]
    );
    let (ext_pair, ext_make) = (find(&out, "ext_pair").id, find(&out, "ext_make").id);
    let insts: Vec<Inst> = entry(find(&out, "_RF")).body.iter().map(|n| n.inst.clone()).collect();
    assert_eq!(
        insts,
        vec![
            Inst::Alloca { ty: s24.clone(), count: None, align: None },
            Inst::MakeAggregate { ty: tup.clone(), variant: None, fields: vec![v(0), v(0)] },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(1), field: 0 },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(1), field: 1 },
            Inst::Call { callee: ext_pair, args: vec![v(5), v(6)] },
            Inst::Call { callee: ext_make, args: vec![v(7), v(2)] },
            Inst::Load { ty: s24.clone(), ptr: v(7), volatile: false, align: None },
            Inst::ExtractField { ty: Ty::U64, aggregate: v(3), field: 1 },
            Inst::Return { values: vec![v(4)] },
        ]
    );
    assert_eq!(
        out.placements["ext_pair"].params,
        vec![ParamPlace::Pair(ScalarPlace::gpr(0, 64), ScalarPlace::gpr(1, 64))]
    );
    assert_eq!(out.placements["ext_make"].ret, ReturnPlace::Indirect);

    // A genuine mismatch and an outside-the-subset shape are told apart.
    let p = &fx.m;
    let pair_ty = p.func_types
        [p.functions.iter().find(|f| f.name == "ext_pair").unwrap().ty.as_usize()]
    .clone();
    let wide = pair(scalar(64, INT), scalar(32, INT), PairOf::Fields([0, 1]));
    assert!(matches!(
        legalize_signature(p, &pair_ty, &abi(vec![wide], direct(64))),
        Err(AbiDisagreement::Mismatch(_))
    ));
    assert!(matches!(
        legalize_signature(p, &pair_ty, &abi(vec![ArgShape::Cast], direct(64))),
        Err(AbiDisagreement::OutsideSubset(_))
    ));
    fx.declarations.insert("ext_pair".into(), abi(vec![ArgShape::Cast], direct(64)));
    refused_with(&fx.run(), RefusalClass::CalleeAbiMismatch, "_RF", "ext_pair");
}
