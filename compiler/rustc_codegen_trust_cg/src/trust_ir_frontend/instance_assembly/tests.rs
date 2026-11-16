// ---------------------------------------------------------------------------
// The PURE half of the instance lane: `trust_ir::Module` in, `Result` out. No
// `TyCtxt`, no `Session`. The shapes are the goal subject's (step 2 increment 3):
// `f` (extern "C", the handoff body) calls `ident::<u64>`, a bodyless
// declaration in the assembled module, and the instance lane appends the
// instance body and relinks `f`'s call edge to it.
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;

use trust_ir::value::{BlockId, FuncId, FuncTyId, GlobalId, StructId, TyId, ValueId};
use trust_ir::{
    BinOp, Block, BodyGate, CallingConv, Constant, FieldDef, FuncTy, Function, Global, InstrNode,
    Linkage, Module, Producer, SourceSpan, StructDef, TupleLayoutDescriptor, Ty,
};

use super::*;

#[test]
fn upstream_local_copy_takes_the_upstream_slot() {
    assert_eq!(origin_for(true, true), OriginChoice::Upstream);
    assert_eq!(origin_for(false, true), OriginChoice::Local);
    assert_eq!(origin_for(false, false), OriginChoice::Local);
}

#[test]
fn an_upstream_instance_rustc_links_is_never_spliced() {
    assert_eq!(origin_for(true, false), OriginChoice::Linked);
    assert_ne!(origin_for(true, false), OriginChoice::Upstream);
}

#[test]
fn d17_strict_condition_unchanged_for_upstream_bodies() {
    assert!(
        super::super::upstream_entry::require_strict(strict_gate_from(false, "strict")).is_ok()
    );
    for policy in ["off", "allow-unknown", "unrecognized"] {
        assert!(
            super::super::upstream_entry::require_strict(strict_gate_from(false, policy)).is_err()
        );
    }
    assert!(super::super::upstream_entry::require_strict(strict_gate_from(true, "off")).is_err());
    assert!(
        super::super::upstream_entry::require_strict(strict_gate_from(true, "allow-unknown"))
            .is_ok()
    );
}

const IDENT: &str = "_RINvCs0_12inc3_subject5identyEB2_";
const DIRECT: &str = "trust-direct-lane-structural";

fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

fn sig(param: Ty, ret: Ty) -> FuncTy {
    FuncTy { params: vec![param], returns: vec![ret], is_vararg: false, abi: None }
}

fn declaration(id: u32, name: &str, ty: FuncTyId, conv: CallingConv) -> Function {
    let mut f = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
    f.calling_conv = conv;
    f.linkage = Linkage::External;
    f.producer = Some(Producer::TRust);
    f
}

/// `fn(x) { ret x }`.
fn ident_body(id: u32, name: &str, ty: FuncTyId, param: Ty) -> Function {
    let mut f = declaration(id, name, ty, CallingConv::Rust);
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), param);
    entry.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    f.blocks.push(entry);
    f
}

/// `fn f(x) { %1 = call callee(x); %2 = const k; %3 = xor %1, %2; ret %3 }`, with a span in
/// source file `file`.
fn caller_body(id: u32, name: &str, ty: FuncTyId, callee: FuncId, k: i64, file: u32) -> Function {
    let mut f = declaration(id, name, ty, CallingConv::C);
    let span = SourceSpan { file, line: 5, col: 38 };
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    entry.body.push(
        InstrNode::new(Inst::Call { callee, args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1))
            .with_span(span),
    );
    entry.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(k.into()) })
            .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Xor,
            ty: Ty::U64,
            lhs: ValueId::new(1),
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }));
    f.blocks.push(entry);
    f
}

/// The assembled module as finalization leaves it for the goal: body `f` (gated by the direct
/// lane) calls the bodyless declaration `ident`.
fn host() -> Module {
    let mut m = Module::new("inc3_subject");
    m.target_info = Some(target());
    m.files.push("inc3_subject.rs".to_string());
    let ty = m.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    let mut f = caller_body(0, "f", ty, FuncId::new(1), 7, 0);
    f.body_gate = Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
    m.try_add_function(f).expect("Module::try_add_function: test fixture");
    m.try_add_function(declaration(1, "ident", ty, CallingConv::Rust))
        .expect("Module::try_add_function: test fixture");
    m
}

/// `ident::<u64>`'s instance module: the body alone.
fn ident_guest() -> Module {
    let mut m = Module::new("inc3_subject");
    let ty = m.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    m.try_add_function(ident_body(0, IDENT, ty, Ty::U64))
        .expect("Module::try_add_function: test fixture");
    m
}

/// `f`'s instance module: the body plus one signed declaration of `ident::<u64>`.
fn f_guest(k: i64) -> Module {
    let mut m = Module::new("inc3_subject");
    m.files.push("inc3_subject.rs".to_string());
    let ty = m.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    m.try_add_function(caller_body(0, "f", ty, FuncId::new(1), k, 0))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(declaration(1, IDENT, ty, CallingConv::Rust))
        .expect("Module::try_add_function: test fixture");
    m
}

/// The relink's identity check, as the pure tests model it: the host declaration of the goal is
/// named `ident`, and it names the guest edge `FuncId(1)` (the rustc half asks
/// `trust_thir_lower::instance_admission::declaration_names_instance` instead).
fn names_ident(name: &str, guest_edge: FuncId) -> Result<(), String> {
    if name == "ident" && guest_edge == FuncId::new(1) {
        Ok(())
    } else {
        Err(format!("`{name}` does not name guest edge FuncId({})", guest_edge.index()))
    }
}

fn edges(pairs: &[(u32, u32)]) -> BTreeMap<FuncId, FuncId> {
    pairs.iter().map(|&(k, t)| (FuncId::new(k), FuncId::new(t))).collect()
}

fn callees(function: &Function) -> Vec<FuncId> {
    function
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .filter_map(|n| match n.inst {
            Inst::Call { callee, .. } => Some(callee),
            _ => None,
        })
        .collect()
}

// ---- the census predicates and the lane --------------------------------

#[test]
fn reaches_declaration_is_transitive() {
    let mut m = Module::new("k");
    let ty = m.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    m.try_add_function(caller_body(0, "f", ty, FuncId::new(1), 1, 0))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(caller_body(1, "g", ty, FuncId::new(2), 2, 0))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(declaration(2, "h", ty, CallingConv::Rust))
        .expect("Module::try_add_function: test fixture");
    assert!(reaches_declaration(&m, FuncId::new(0)), "f -> g (body) -> h (declaration)");
    assert!(!is_leaf(&m, FuncId::new(0)));

    let mut linked = Module::new("k");
    let ty =
        linked.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    linked
        .try_add_function(caller_body(0, "f", ty, FuncId::new(1), 1, 0))
        .expect("Module::try_add_function: test fixture");
    linked
        .try_add_function(ident_body(1, "g", ty, Ty::U64))
        .expect("Module::try_add_function: test fixture");
    assert!(!reaches_declaration(&linked, FuncId::new(0)), "f -> g (body) only");
    assert!(!reaches_clean_body(&linked, FuncId::new(0)));
    assert!(is_leaf(&linked, FuncId::new(1)));

    linked.functions[1].producer = Some(Producer::Clean);
    assert!(reaches_clean_body(&linked, FuncId::new(0)), "f -> a Clean-origin body");
}

#[test]
fn lane_plan_table() {
    assert_eq!(lane_for(true, false, false), LaneChoice::Instance, "generic");
    assert_eq!(lane_for(true, true, true), LaneChoice::Instance, "generic, whatever it reaches");
    assert_eq!(lane_for(false, true, false), LaneChoice::Instance, "mono reaching a declaration");
    assert_eq!(lane_for(false, false, false), LaneChoice::Handoff, "mono, fully linked");
    assert_eq!(lane_for(false, true, true), LaneChoice::Handoff, "mono reaching Clean");
    assert_eq!(lane_for(false, false, true), LaneChoice::Handoff);
}

// ---- append and relink: the goal's shape --------------------------------

#[test]
fn splice_appends_a_table_free_body_and_rewrites_its_call_edge() {
    let mut star = host();
    let base = star.clone();
    let id = append_instance_body(None, &mut star, &ident_guest(), 0, true, &BTreeMap::new())
        .expect("a table-free leaf instance body is spliced");
    assert_eq!(id, FuncId::new(2), "appended at the next dense id");
    let appended = star.function_by_id(id).unwrap();
    assert_eq!(appended.id, id);
    assert_eq!(appended.name, IDENT, "the guest's mangled symbol");
    assert_eq!(appended.ty, FuncTyId::new(0), "the signature dedups onto the host's row");
    assert_eq!(appended.blocks, ident_guest().functions[0].blocks);
    assert_eq!(appended.calling_conv, CallingConv::Rust);
    assert_eq!(
        appended.body_gate,
        Some(BodyGate::Gated {
            authority: TRUST_INSTANCE_LANE_AUTHORITY.to_string(),
            evidence: None
        }),
        "an appended body names the instance lane as its authority, never None"
    );
    assert_eq!(tables_unchanged(&base, &star), Ok(()));
    assert!(!reaches_declaration(&star, id));
    assert_eq!(star.func_types.len(), 1, "no signature row added");

    relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &f_guest(7),
        1,
        true,
        &edges(&[(1, 2)]),
        &names_ident,
    )
    .expect("the instance lowering of `f` is the assembled body modulo callee ids");
    let f = star.function_by_id(FuncId::new(0)).unwrap();
    assert_eq!(callees(f), vec![FuncId::new(2)], "the call now names the spliced instance");
    assert_eq!(f.name, "f");
    assert_eq!(f.calling_conv, CallingConv::C);
    assert_eq!(f.linkage, Linkage::External);
    assert_eq!(
        f.body_gate,
        Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None }),
        "a relinked body keeps the gate finalize stamped"
    );
    assert!(!reaches_declaration(&star, FuncId::new(0)));
    assert_eq!(tables_unchanged(&base, &star), Ok(()));
    assert_eq!(body_gates_are_stamped(&star), Ok(()));
}

#[test]
fn every_body_of_star_carries_a_body_gate() {
    let mut star = host();
    let id = append_instance_body(None, &mut star, &ident_guest(), 0, true, &BTreeMap::new()).unwrap();
    relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &f_guest(7),
        1,
        true,
        &edges(&[(1, 2)]),
        &names_ident,
    )
    .unwrap();
    for function in star.functions.iter().filter(|f| !f.blocks.is_empty()) {
        assert!(function.body_gate.is_some(), "{} carries no body gate", function.name);
    }
    assert_eq!(body_gates_are_stamped(&star), Ok(()));
    // The tripwire itself: one body with NO claim refuses the whole module.
    star.function_by_id_mut(id).unwrap().body_gate = None;
    let refused = body_gates_are_stamped(&star).unwrap_err();
    assert!(refused.contains(IDENT), "{refused}");
}

/// The RELINK-DIVERGENCE CONTROL: an instance lowering that is not the assembled body — here the
/// xor constant differs — is refused, and the host is untouched.
#[test]
fn a_diverging_instance_lowering_never_relinks() {
    let mut star = host();
    append_instance_body(None, &mut star, &ident_guest(), 0, true, &BTreeMap::new()).unwrap();
    let before = star.clone();
    let error = relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &f_guest(8),
        1,
        true,
        &edges(&[(1, 2)]),
        &names_ident,
    )
    .unwrap_err();
    assert!(error.contains("instance lowering diverges from the assembled body"), "{error}");
    assert_eq!(star, before, "a refused relink is transactional");

    // A different signature diverges too.
    let mut wide = f_guest(7);
    wide.func_types[0] = sig(Ty::U32, Ty::U32);
    let error = relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &wide,
        1,
        true,
        &edges(&[(1, 2)]),
        &names_ident,
    )
    .unwrap_err();
    assert!(error.contains("signature"), "{error}");
    assert_eq!(star, before);
}

#[test]
fn a_relink_never_retargets_a_linked_body_edge() {
    // `f` already calls the BODY `g`; the instance lane may not point that edge anywhere else.
    let mut star = Module::new("k");
    let ty =
        star.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    star.try_add_function(caller_body(0, "f", ty, FuncId::new(1), 7, 0))
        .expect("Module::try_add_function: test fixture");
    star.try_add_function(ident_body(1, "g", ty, Ty::U64))
        .expect("Module::try_add_function: test fixture");
    star.try_add_function(ident_body(2, "other", ty, Ty::U64))
        .expect("Module::try_add_function: test fixture");
    for f in &mut star.functions {
        f.body_gate = Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
    }
    let mut guest = f_guest(7);
    guest.files.clear();
    guest.functions[0].blocks[0].body[0].span = None;
    star.functions[0].blocks[0].body[0].span = None;
    let before = star.clone();
    let error = relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &guest,
        1,
        true,
        &edges(&[(1, 2)]),
        &names_ident,
    )
    .unwrap_err();
    assert!(error.contains("never retargeted"), "{error}");
    assert_eq!(star, before);
    // Mapped to the very body it links, the relink is the identity.
    relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &guest,
        1,
        true,
        &edges(&[(1, 1)]),
        &names_ident,
    )
    .unwrap();
    assert_eq!(star, before);
}

#[test]
fn body_correspondence_is_a_bijection() {
    // Host: two distinct callees. Guest: one callee twice.
    let mut host = Module::new("k");
    let ty =
        host.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    let mut f = caller_body(0, "f", ty, FuncId::new(1), 7, 0);
    let mut second = f.blocks[0].body[0].clone();
    second.inst = Inst::Call { callee: FuncId::new(2), args: vec![ValueId::new(0)] };
    second.results = vec![ValueId::new(9)];
    second.span = None;
    f.blocks[0].body.insert(1, second.clone());
    f.blocks[0].body[0].span = None;
    let mut g = f.clone();
    if let Inst::Call { callee, .. } = &mut g.blocks[0].body[1].inst {
        *callee = FuncId::new(1);
    }
    let error = body_correspondence(&f, &[], &g, &[]).unwrap_err();
    assert!(error.contains("one to one"), "{error}");
    assert_eq!(
        body_correspondence(&f, &[], &f, &[]),
        Ok(vec![(FuncId::new(1), FuncId::new(1)), (FuncId::new(2), FuncId::new(2))])
    );
}

// ---- the per-edge signature check --------------------------------------

/// One caller's edge disagrees with the body it would call and is refused, NAMING the edge; a
/// second caller of the same body still splices, and the refused one left no trace.
#[test]
fn a_per_edge_signature_mismatch_refuses_that_caller_only() {
    let mut star = host();
    append_instance_body(None, &mut star, &ident_guest(), 0, true, &BTreeMap::new()).unwrap();

    // Caller A declares `ident::<u64>` as `fn(u32) -> u32`.
    let mut a = Module::new("k");
    let wide = a.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    let narrow =
        a.add_func_type(sig(Ty::U32, Ty::U32)).expect("Module::add_func_type: test fixture");
    a.try_add_function(caller_body(0, "_RNvCs0_1k1a", wide, FuncId::new(1), 1, 0))
        .expect("Module::try_add_function: test fixture");
    a.try_add_function(declaration(1, IDENT, narrow, CallingConv::Rust))
        .expect("Module::try_add_function: test fixture");
    a.files.push("inc3_subject.rs".to_string());
    let before = star.clone();
    let error = append_instance_body(None, &mut star, &a, 1, true, &edges(&[(1, 2)])).unwrap_err();
    assert!(error.contains("signature mismatch on edge FuncId(1)"), "{error}");
    assert!(error.contains(IDENT), "the refusal names the edge: {error}");
    assert_eq!(star, before, "the refused caller left no trace");

    // A calling-convention disagreement is a signature mismatch too.
    let mut c = a.clone();
    c.functions[0].name = "_RNvCs0_1k1c".to_string();
    c.functions[1].ty = wide;
    c.functions[1].calling_conv = CallingConv::C;
    let error = append_instance_body(None, &mut star, &c, 1, true, &edges(&[(1, 2)])).unwrap_err();
    assert!(error.contains("signature mismatch"), "{error}");

    // Caller B declares it truthfully and splices into the same module.
    let mut b = a.clone();
    b.functions[0].name = "_RNvCs0_1k1b".to_string();
    b.functions[1].ty = wide;
    let id = append_instance_body(None, &mut star, &b, 1, true, &edges(&[(1, 2)])).unwrap();
    assert_eq!(callees(star.function_by_id(id).unwrap()), vec![FuncId::new(2)]);
}

#[test]
fn check_edges_requires_every_declaration_mapped_to_a_body() {
    let star = host();
    let guest = f_guest(7);
    assert!(check_edges(&star, &guest, 1, &edges(&[])).unwrap_err().contains("edge map"));
    assert!(check_edges(&star, &guest, 1, &edges(&[(1, 9)])).unwrap_err().contains("lacks"));
    assert!(
        check_edges(&star, &guest, 1, &edges(&[(1, 1)])).unwrap_err().contains("bodyless"),
        "an edge may never map onto a declaration"
    );
}

// ---- the splice preconditions ------------------------------------------

#[test]
fn splice_refuses_an_unmapped_edge() {
    let mut star = host();
    let before = star.clone();
    let error =
        append_instance_body(None, &mut star, &f_guest(7), 1, true, &BTreeMap::new()).unwrap_err();
    assert!(error.contains("edge map"), "{error}");
    assert_eq!(star, before);
}

#[test]
fn splice_refuses_a_guest_that_names_a_table_or_a_fn_pointer() {
    let mut cases: Vec<(&str, Module, bool)> = Vec::new();

    // A struct def and a `Ty::Struct(0)` parameter.
    let mut with_struct = ident_guest();
    with_struct.structs.push(StructDef {
        id: StructId::new(0),
        name: "S".to_string(),
        fields: vec![FieldDef { name: "0".to_string(), ty: Ty::U64, offset: Some(0) }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    with_struct.func_types[0] = sig(Ty::Struct(StructId::new(0)), Ty::U64);
    with_struct.functions[0].blocks[0].params[0].1 = Ty::Struct(StructId::new(0));
    cases.push(("structs", with_struct, true));

    // A global and a `GlobalAddr` of it.
    let mut with_global = ident_guest();
    with_global.globals.push(Global {
        name: "G".to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(1.into())),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    with_global.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(ValueId::new(5)),
    );
    cases.push(("globals", with_global, true));

    // An inline tuple, which pends a `types` row and a tuple layout the census cannot see.
    let mut with_tuple = ident_guest();
    let tuple = with_tuple
        .add_type(Ty::Tuple(vec![Ty::U64, Ty::U64]))
        .expect("Module::add_type: test fixture");
    with_tuple.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: tuple,
        size: 16,
        align: 8,
        field_offsets: vec![0, 8],
    });
    cases.push(("types", with_tuple, true));

    // A `CallIndirect`.
    let mut indirect = ident_guest();
    indirect.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![ValueId::new(0)],
            calling_conv: CallingConv::Rust,
        })
        .with_result(ValueId::new(5)),
    );
    cases.push(("names", indirect, true));

    // A `Const FnDef` — a first-class function value.
    let mut fn_def = ident_guest();
    fn_def.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::Func(FuncTyId::new(0)),
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(5)),
    );
    cases.push(("names", fn_def, true));

    // The producer's own fn-pointer verdict.
    cases.push(("function pointer", ident_guest(), false));

    // A drop.
    let mut dropping = ident_guest();
    dropping.functions[0].blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::Drop { ty: Ty::U64, ptr: ValueId::new(0) }));
    cases.push(("Drop", dropping, true));

    for (needle, guest, fn_pointer_free) in cases {
        let mut star = host();
        let before = star.clone();
        let error = append_instance_body(None, &mut star, &guest, 0, fn_pointer_free, &BTreeMap::new())
            .expect_err(needle);
        assert!(error.contains(needle), "expected `{needle}` in: {error}");
        assert_eq!(star, before, "`{needle}`: the host is unchanged");
    }
}

#[test]
fn splice_reinterns_span_files() {
    let mut star = Module::new("k");
    star.files = vec!["b.rs".to_string()];
    let ty =
        star.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    let mut target = ident_body(0, "t", ty, Ty::U64);
    target.body_gate = Some(BodyGate::Gated { authority: DIRECT.to_string(), evidence: None });
    star.try_add_function(target).expect("Module::try_add_function: test fixture");

    let mut guest = Module::new("k");
    guest.files = vec!["a.rs".to_string(), "b.rs".to_string()];
    let gty =
        guest.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    let mut body = caller_body(0, "_RNvCs0_1k1g", gty, FuncId::new(1), 3, 1);
    body.blocks[0].body[1].span = Some(SourceSpan { file: 0, line: 1, col: 1 });
    guest.try_add_function(body).expect("Module::try_add_function: test fixture");
    guest
        .try_add_function(declaration(1, "t", gty, CallingConv::Rust))
        .expect("Module::try_add_function: test fixture");

    let id = append_instance_body(None, &mut star, &guest, 1, true, &edges(&[(1, 0)])).unwrap();
    assert_eq!(star.files, vec!["b.rs".to_string(), "a.rs".to_string()], "a.rs is appended");
    let spliced = star.function_by_id(id).unwrap();
    assert_eq!(spliced.blocks[0].body[0].span.unwrap().file, 0, "b.rs: guest #1 -> host #0");
    assert_eq!(spliced.blocks[0].body[1].span.unwrap().file, 1, "a.rs: guest #0 -> host #1");
}

#[test]
fn tables_unchanged_compares_tuple_layouts_too() {
    let base = host();
    let mut star = base.clone();
    assert_eq!(tables_unchanged(&base, &star), Ok(()));
    star.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 16,
        align: 8,
        field_offsets: vec![0, 8],
    });
    assert!(tables_unchanged(&base, &star).unwrap_err().contains("tuple_layouts"));
}

#[test]
fn tables_unchanged_compares_closure_layouts_too() {
    let base = host();
    let mut changed = base.clone();
    changed.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
        origin: None,
        closure: trust_ir::ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    assert!(tables_unchanged(&base, &changed).unwrap_err().contains("closure_layouts"));
}

// ---- the review's fix-before-freeze rows ---------------------------------

/// The RELINK checks each host DECLARATION's identity against the instance the guest edge
/// resolved to, not only instruction position and the FuncId bijection.
#[test]
fn a_relink_refuses_a_host_declaration_that_names_another_instance() {
    let mut star = host();
    append_instance_body(None, &mut star, &ident_guest(), 0, true, &BTreeMap::new()).unwrap();
    let before = star.clone();
    let refuse_all = |name: &str, _: FuncId| -> Result<(), String> {
        Err(format!("`{name}` keys another instance"))
    };
    let error = relink_monomorphic_body(
        &mut star,
        FuncId::new(0),
        &f_guest(7),
        1,
        true,
        &edges(&[(1, 2)]),
        &refuse_all,
    )
    .unwrap_err();
    assert!(error.contains("does not name the instance its guest edge"), "{error}");
    assert!(error.contains("`ident` keys another instance"), "{error}");
    assert_eq!(star, before, "transactional");
    // The same relink with the declaration renamed: the goal's own identity check refuses it.
    star.function_by_id_mut(FuncId::new(1)).unwrap().name = "other".to_string();
    let renamed = star.clone();
    assert!(
        relink_monomorphic_body(
            &mut star,
            FuncId::new(0),
            &f_guest(7),
            1,
            true,
            &edges(&[(1, 2)]),
            &names_ident,
        )
        .is_err()
    );
    assert_eq!(star, renamed);
}

/// A self-recursive monomorphic body is NOT a leaf: its self edge is a cycle, refused
/// `[instance-assembly]` like every other one, never linked "as it is".
#[test]
fn a_self_recursive_body_is_not_a_leaf() {
    let mut m = Module::new("k");
    let ty = m.add_func_type(sig(Ty::U64, Ty::U64)).expect("Module::add_func_type: test fixture");
    m.try_add_function(ident_body(0, "leaf", ty, Ty::U64))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(caller_body(1, "recurse", ty, FuncId::new(1), 1, 0))
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(caller_body(2, "caller", ty, FuncId::new(0), 1, 0))
        .expect("Module::try_add_function: test fixture");
    assert!(is_leaf(&m, FuncId::new(0)));
    assert!(!is_leaf(&m, FuncId::new(1)), "a self edge is a call");
    assert!(!is_leaf(&m, FuncId::new(2)), "calling a leaf is a call");
    assert!(!reaches_declaration(&m, FuncId::new(1)));
}

/// The instance lane admits NO instruction the handoff's splice refuses: `Invoke` (refused by
/// name there) and every variant `crate_module::inst_embedded_tys` does not model.
#[test]
fn the_splice_admits_no_instruction_the_handoff_splice_refuses() {
    use trust_ir::Ordering;
    use trust_ir::inst::AllocOrigin;
    let v = ValueId::new(0);
    let refused = [
        Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: BlockId::new(0),
            normal_args: vec![],
            unwind_dest: BlockId::new(0),
        },
        Inst::MemCopy { dst: v, src: v, bytes: v, overlap: false },
        Inst::MemSet { dst: v, byte: v, bytes: v },
        Inst::Fence { ordering: Ordering::SeqCst },
        Inst::AtomicLoad { ty: Ty::U64, ptr: v, ordering: Ordering::SeqCst },
        Inst::HeapAlloc { ty: Ty::U64, count: None, align: None, origin: AllocOrigin::RustHeap },
        Inst::Dealloc { ptr: v },
        Inst::Retain { ptr: v },
        Inst::Release { ptr: v },
        Inst::IsUnique { ptr: v },
        Inst::Borrow { ptr: v },
        Inst::MakeAggregate { ty: Ty::U64, variant: None, fields: vec![] },
        Inst::LandingPad { is_cleanup: true, catch_type_indices: vec![] },
        Inst::Resume { exn: v },
        Inst::CloseFrame { frame: v },
        Inst::Drop { ty: Ty::U64, ptr: v },
        // Trust (trust-ir v54): a SITED assert names its panic entry and location, which no
        // splice pass remaps; the unwinding and no-unwind twins (v53/v55/v56) are unmodeled too.
        Inst::Assert {
            cond: v,
            kind: trust_ir::AssertKind::Unspecified,
            site: Some(trust_ir::PanicSite {
                entry: FuncId::new(1),
                location: trust_ir::PanicLocation::Value(v),
            }),
        },
        Inst::AssertInvoke {
            cond: v,
            kind: trust_ir::AssertKind::Unspecified,
            site: trust_ir::PanicSite {
                entry: FuncId::new(1),
                location: trust_ir::PanicLocation::Value(v),
            },
            normal_dest: BlockId::new(0),
            normal_args: vec![],
            unwind_dest: BlockId::new(0),
        },
        Inst::CallCannotUnwind { callee: FuncId::new(1), args: vec![] },
        Inst::CallIndirectCannotUnwind {
            callee: v,
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::Rust,
        },
        Inst::DropInvoke {
            ty: Ty::U64,
            ptr: v,
            normal_dest: BlockId::new(0),
            normal_args: vec![],
            unwind_dest: BlockId::new(0),
        },
        Inst::InvokeIndirect {
            callee: v,
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::Rust,
            normal_dest: BlockId::new(0),
            normal_args: vec![],
            unwind_dest: BlockId::new(0),
        },
    ];
    for inst in refused {
        assert!(!instruction_is_spliceable(&inst), "admitted: {inst:?}");
        let mut guest = ident_guest();
        guest.functions[0].blocks[0].body.insert(0, InstrNode::new(inst.clone()));
        let mut star = host();
        let before = star.clone();
        let error = append_instance_body(None, &mut star, &guest, 0, true, &BTreeMap::new())
            .expect_err("refused");
        assert!(error.contains("does not model"), "{inst:?}: {error}");
        assert_eq!(star, before);
    }
    // The modeled set stays admitted.
    for inst in [
        Inst::Return { values: vec![] },
        Inst::Call { callee: FuncId::new(1), args: vec![] },
        Inst::Assert { cond: v, kind: trust_ir::AssertKind::Unspecified, site: None },
        Inst::Assert {
            cond: v,
            kind: trust_ir::AssertKind::BoundsCheck { index: v, len: v },
            site: None,
        },
        Inst::Unreachable,
        Inst::Const { ty: Ty::U64, value: Constant::Int(1) },
    ] {
        assert!(instruction_is_spliceable(&inst), "refused: {inst:?}");
    }
}

/// EVERY row of the explicit table-freedom list refuses on its own — including `tuple_layouts`
/// alone, `completeness`, and the proof tables — so dropping a row from the frozen list fails
/// here.
#[test]
fn every_table_freedom_row_refuses_on_its_own() {
    let mut cases: Vec<(&str, Module)> = Vec::new();
    let with = |edit: &dyn Fn(&mut Module)| {
        let mut m = ident_guest();
        edit(&mut m);
        m
    };
    cases.push((
        "structs",
        with(&|m| {
            m.structs.push(StructDef {
                id: StructId::new(0),
                name: "S".into(),
                fields: vec![],
                size: Some(0),
                align: Some(1),
                repr: Default::default(),
                origin: None,
            })
        }),
    ));
    cases.push((
        "enums",
        with(&|m| {
            m.enums.push(trust_ir::EnumDef {
                id: trust_ir::value::EnumId::new(0),
                name: "E".into(),
                variants: vec![],
                discriminants: vec![],
                layout: None,
                repr: None,
                origin: None,
            })
        }),
    ));
    cases.push((
        "records",
        with(&|m| {
            m.records.push(trust_ir::RecordDef {
                id: trust_ir::value::RecordId::new(0),
                name: "R".into(),
                fields: vec![],
            })
        }),
    ));
    cases.push((
        "closure_types",
        with(&|m| {
            m.closure_types.push(trust_ir::ClosureTy { func: FuncTyId::new(0), captures: vec![] })
        }),
    ));
    cases.push((
        "globals",
        with(&|m| {
            m.globals.push(Global {
                name: "G".into(),
                ty: Ty::U64,
                mutable: false,
                initializer: Some(Constant::Int(0)),
                linkage: Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: Default::default(),
                retained: false,
            })
        }),
    ));
    cases.push((
        "types",
        with(&|m| {
            m.add_type(Ty::U64).expect("Module::add_type: test fixture");
        }),
    ));
    cases.push((
        "tuple_layouts",
        with(&|m| {
            m.tuple_layouts.push(TupleLayoutDescriptor {
                tuple_type: TyId::new(0),
                size: 16,
                align: 8,
                field_offsets: vec![0, 8],
            })
        }),
    ));
    cases.push(("predicates", with(&|m| m.predicates.push(trust_ir::Pred::Top))));
    cases.push((
        "universes",
        with(&|m| m.universes.push(trust_ir::Universe::IntRange { lo: 0, hi: 1 })),
    ));
    cases.push(("global_asm", with(&|m| m.global_asm.push("nop".into()))));
    cases.push((
        "imports",
        with(&|m| {
            m.imports.push(trust_ir::ModuleImport::new(
                "dep",
                trust_ir::proof::ProofDigest::sha256_domain("t", b"x"),
            ))
        }),
    ));
    cases.push((
        "proof_obligations",
        with(&|m| {
            m.proof_obligations.push(trust_ir::proof::ProofObligation::new(
                trust_ir::value::ProofId::new(0),
                trust_ir::proof::ObligationKind::ArithmeticSafety,
                trust_ir::proof::ProofStatus::Pending,
                "o",
            ))
        }),
    ));
    cases.push(("spec_modules", with(&|m| m.spec_modules.push(trust_ir::SpecModule::new("s")))));
    cases.push((
        "proof_certificates",
        with(&|m| {
            m.proof_certificates.push(trust_ir::ProofCertificate {
                obligation: trust_ir::value::ProofId::new(0),
                prover: "p".into(),
                evidence: trust_ir::ProofEvidence::Trusted("t".into()),
                assurance: None,
            })
        }),
    ));
    cases.push((
        "obligation_diagnostics",
        with(&|m| {
            m.obligation_diagnostics.push(trust_ir::proof::ObligationDiagnostic::error(
                trust_ir::value::ProofId::new(0),
                "d",
            ))
        }),
    ));
    cases.push((
        "completeness",
        with(&|m| m.completeness = Some(trust_ir::ModuleCompleteness::Complete)),
    ));
    // Trust (trust-ir v55): the drop-glue table keys glue functions by type.
    cases.push((
        "drop_glue",
        with(&|m| m.drop_glue.push(trust_ir::DropGlueEntry { glue: FuncId::new(0), ty: Ty::Ptr })),
    ));
    // Trust (trust-ir v58): the closure-frame table keys frames by `ClosureTyId`.
    cases.push((
        "closure_layouts",
        with(&|m| {
            m.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
                origin: None,
                closure: trust_ir::ClosureTyId::new(0),
                size: 8,
                align: 8,
                capture_offsets: vec![0],
            })
        }),
    ));
    for (needle, guest) in cases {
        let mut star = host();
        let before = star.clone();
        let error =
            append_instance_body(None, &mut star, &guest, 0, true, &BTreeMap::new()).expect_err(needle);
        assert!(error.contains(needle), "expected `{needle}` in: {error}");
        assert_eq!(star, before, "`{needle}`: the host is unchanged");
    }
}

/// The admission token must name the instance the assembler asked for: a body admitted for one
/// instance is refused for another (round-3 token check, negatively).
/// trust-ir D1b: a table door refuses instead of panicking, and the splice maps the refusal
/// into its own error after restoring the host. Here `Module::try_add_function` refuses: the
/// guest body's function-level claim needs an obligation id, and the host's obligation table
/// already holds the last one.
#[test]
fn a_refused_table_door_refuses_the_splice_and_leaves_the_host_unchanged() {
    let mut star = host();
    star.proof_obligations.push(
        trust_ir::proof::ProofObligation::new(
            trust_ir::value::ProofId::new(u32::MAX),
            trust_ir::proof::ObligationKind::PanicFreedom,
            trust_ir::proof::ProofStatus::Pending,
            "holds the last obligation id",
        )
        .with_function(FuncId::new(0)),
    );
    let base = star.clone();
    let mut guest = ident_guest();
    guest.functions[0].proofs.push(trust_ir::proof::ProofAnnotation::NoPanic);
    let refusal = append_instance_body(None, &mut star, &guest, 0, true, &BTreeMap::new())
        .expect_err("an exhausted obligation id space refuses the splice");
    assert!(refusal.contains("exhausted"), "the refusal names the exhausted space: {refusal}");
    assert_eq!(star, base, "a refused splice leaves every host table as it was");

    // The same guest without the claim still splices: the refusal is the door's, not the body's.
    let mut star = base.clone();
    append_instance_body(None, &mut star, &ident_guest(), 0, true, &BTreeMap::new())
        .expect("a claim-free guest still splices into the same host");
}

#[test]
fn a_token_for_another_instance_is_refused() {
    assert_eq!(token_names(7u32, 7u32), Ok(()));
    let error = token_names(7u32, 8u32).expect_err("a token for another instance");
    assert!(error.contains("names another instance (7)"), "{error}");
}

/// CONTENT binding: the body and each declaration must carry the link-time symbol of the
/// instance they stand for; a renamed function, or a missing one, is refused.
#[test]
fn a_function_not_named_by_its_instances_symbol_is_refused() {
    let module = host();
    let name = module.functions[0].name.clone();
    assert_eq!(function_is_named(&module, module.functions[0].id, &name), Ok(()));
    let error = function_is_named(&module, module.functions[0].id, "_RNvCs0_1k9other")
        .expect_err("a different symbol");
    assert!(error.contains("not `_RNvCs0_1k9other`"), "{error}");
    let missing = function_is_named(&module, FuncId::new(9_999), &name).expect_err("missing");
    assert!(missing.contains("is missing"), "{missing}");
}
