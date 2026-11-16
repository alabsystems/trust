//! Unit tests for the frozen instance-lane admission file. NOT frozen (the manifest's tests rule).
//! They pin the post-lowering gate (whose facts and token are private to the frozen file, so its
//! tests live here), the fail-closed lane, the recording, the per-edge decision over re-derived
//! call sites (`decide_edge`: a site resolving to another item, to a non-item, a conflicting
//! record, a concretely keyed edge never recorded), the declaration-identity matcher and the
//! monomorphic-local predicate. None needs a `TyCtxt`: the `TyCtxt` halves (`resolve_site`,
//! `edge_refusal_text`) only compute the inputs and render the refusals these pin; the run-make
//! row `trust-cg-f1-generic-instance` (an intrinsic called from a generic body) exercises them.

use rustc_span::def_id::{DefId, DefIndex, LOCAL_CRATE};

use super::*;

fn def(index: u32) -> DefId {
    DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(index) }
}

fn record<'tcx>(func: u32, callee: u32, is_item: bool) -> CalleeInstanceRecord<'tcx> {
    CalleeInstanceRecord {
        func_id: FuncId::new(func),
        def: def(callee),
        args: ty::GenericArgs::empty(),
        is_item,
        site_def: def(callee),
        site_args: ty::GenericArgs::empty(),
    }
}

fn the_instance() -> ty::Instance<'static> {
    ty::Instance { def: ty::InstanceKind::Item(def(7)), args: ty::GenericArgs::empty() }
}

// ------------------------------------------------------------------ the post-lowering gate

fn clean() -> MonoLoweringFacts<'static> {
    MonoLoweringFacts {
        instance: the_instance(),
        first_unsupported: None,
        symbolic: false,
        opaque_collapse: false,
        undef_placeholder: false,
        param_arm_hits: 0,
        mono_residual: false,
        union_lane: false,
        enum_param_lane: false,
        fnptr_adapter: false,
        pending_consts: 0,
        place_path_carrier: false,
        zst_closure_arg: false,
        coroutine_frame_ptr: false,
        non_fn_body: false,
        drop_bearing: false,
        functions: 1,
    }
}

fn admits(facts: MonoLoweringFacts<'static>) -> Result<(), InstanceRefusal> {
    mono_thir_result_admits(&facts).map(|admitted| {
        assert_eq!(admitted.instance(), facts.instance, "the token names the admitted instance");
    })
}

#[test]
fn a_clean_monomorphic_lowering_is_admitted_and_the_token_names_it() {
    assert_eq!(admits(clean()), Ok(()));
}

/// **(b), AS A TEST.** The `ty::Param` arm is retired BY CONSTRUCTION, not by weakening: if it is
/// ever reached anyway, the instance is REFUSED. There is no fact set in which a param-arm hit
/// yields a Module whose `T` is spelled `Ty::Unit`.
#[test]
fn reaching_the_ty_param_arm_refuses_the_instance_instead_of_emitting_unit_for_t() {
    for hits in [1, u32::MAX] {
        let facts = MonoLoweringFacts { param_arm_hits: hits, ..clean() };
        assert_eq!(admits(facts), Err(InstanceRefusal::MonoIncomplete));
    }
}

/// The other half of the same tripwire, independent of the first.
#[test]
fn a_residual_parameter_refuses_even_with_zero_param_arm_hits() {
    let residual = MonoLoweringFacts { mono_residual: true, ..clean() };
    assert_eq!(residual.param_arm_hits, 0);
    assert_eq!(admits(residual), Err(InstanceRefusal::MonoIncomplete));
}

/// THE FAIL-CLOSED LANE. A lane nobody reported — the lowering's report call removed, or an early
/// return before it — reads as a residual parameter and refuses; a reported lane reads its own
/// tripwires; a second report is a desync.
#[test]
fn an_unreported_lane_refuses_the_instance() {
    let lane = MonoLane::new(ty::GenericArgs::empty());
    assert_eq!(lane_tripwires(&lane), (true, 0));
    let (mono_residual, param_arm_hits) = lane_tripwires(&lane);
    let facts = MonoLoweringFacts { mono_residual, param_arm_hits, ..clean() };
    assert_eq!(admits(facts), Err(InstanceRefusal::MonoIncomplete));
    assert!(lane.callee_instances().is_empty());

    let mut reported = MonoLane::new(ty::GenericArgs::empty());
    reported.report(false, 0, vec![record(1, 10, true)]);
    assert_eq!(lane_tripwires(&reported), (false, 0));
    assert_eq!(reported.callee_instances().len(), 1);
    reported.report(false, 0, Vec::new());
    assert_eq!(lane_tripwires(&reported), (true, 0), "a second report arms the tripwire");

    let mut tripped = MonoLane::new(ty::GenericArgs::empty());
    tripped.report(false, 3, Vec::new());
    assert_eq!(lane_tripwires(&tripped), (false, 3));
}

/// Stronger than `trust_ir_of`'s gate: every placeholder lane is re-refused at the instance seam.
#[test]
fn every_placeholder_lane_is_re_refused_at_the_instance_seam() {
    for (facts, tag) in [
        (MonoLoweringFacts { symbolic: true, ..clean() }, "symbolic"),
        (MonoLoweringFacts { opaque_collapse: true, ..clean() }, "opaque collapse"),
        (MonoLoweringFacts { undef_placeholder: true, ..clean() }, "undef placeholder"),
        (MonoLoweringFacts { union_lane: true, ..clean() }, "union lane"),
        (MonoLoweringFacts { enum_param_lane: true, ..clean() }, "enum param lane"),
        (MonoLoweringFacts { fnptr_adapter: true, ..clean() }, "fn-ptr adapter"),
        (MonoLoweringFacts { place_path_carrier: true, ..clean() }, "place-path carrier"),
        (MonoLoweringFacts { zst_closure_arg: true, ..clean() }, "zst closure arg"),
        (MonoLoweringFacts { coroutine_frame_ptr: true, ..clean() }, "coroutine frame ptr"),
        (MonoLoweringFacts { non_fn_body: true, ..clean() }, "initializer body"),
        (MonoLoweringFacts { drop_bearing: true, ..clean() }, "drop-bearing"),
    ] {
        assert_eq!(admits(facts), Err(InstanceRefusal::LaneRefused(tag)));
    }
}

/// The order is the diagnosis: coverage, the lane's tripwires, the sentinel, the placeholder
/// lanes, drops, and the one-function stamp precondition LAST.
#[test]
fn the_gate_checks_in_its_documented_order() {
    let declined = MonoLoweringFacts {
        first_unsupported: Some("Ty"),
        symbolic: true,
        mono_residual: true,
        ..clean()
    };
    assert_eq!(admits(declined), Err(InstanceRefusal::ProducerDeclined("Ty")));
    let tripped =
        MonoLoweringFacts { symbolic: true, param_arm_hits: 1, pending_consts: 1, ..clean() };
    assert_eq!(admits(tripped), Err(InstanceRefusal::MonoIncomplete));
    let pending = MonoLoweringFacts { pending_consts: 1, symbolic: true, ..clean() };
    assert_eq!(admits(pending), Err(InstanceRefusal::PendingConsts));
    let both = MonoLoweringFacts { drop_bearing: true, functions: 2, ..clean() };
    assert_eq!(admits(both), Err(InstanceRefusal::LaneRefused("drop-bearing")));
    let lane_first = MonoLoweringFacts { symbolic: true, drop_bearing: true, ..clean() };
    assert_eq!(admits(lane_first), Err(InstanceRefusal::LaneRefused("symbolic")));
    // A `&mut self` setter on a struct with a `Vec` sibling field is both opaque-collapsed and
    // drop-bearing (its `*self` place has the struct's type): the placeholder is named first.
    let setter = MonoLoweringFacts { opaque_collapse: true, drop_bearing: true, ..clean() };
    assert_eq!(admits(setter), Err(InstanceRefusal::LaneRefused("opaque collapse")));
    let havoc = MonoLoweringFacts { undef_placeholder: true, drop_bearing: true, ..clean() };
    assert_eq!(admits(havoc), Err(InstanceRefusal::LaneRefused("undef placeholder")));
    for n in [0usize, 2, 7] {
        let facts = MonoLoweringFacts { functions: n, ..clean() };
        assert_eq!(admits(facts), Err(InstanceRefusal::NoBodyFunction));
    }
}

/// Every DISTINCT record is kept; the per-body lane records nothing; the exhausted-id sentinel is
/// skipped; a second, DIFFERENT record for one id arms the tripwire AND stays recorded, so the
/// edge decision refuses it whatever the lowering reports.
#[test]
fn the_recording_keeps_every_distinct_record_and_a_desync_arms_the_tripwire() {
    let mut records = Vec::new();
    let mut residual = false;
    record_callee_instance(&mut records, &mut residual, false, record(1, 10, true));
    assert!(records.is_empty(), "the per-body lane records nothing");
    record_callee_instance(&mut records, &mut residual, true, record(0, 10, true));
    assert!(records.is_empty(), "FuncId(0) is the exhausted-id sentinel");
    record_callee_instance(&mut records, &mut residual, true, record(1, 10, true));
    record_callee_instance(&mut records, &mut residual, true, record(1, 10, true));
    assert_eq!(records.len(), 1, "the same record twice is one record");
    assert!(!residual, "the same record twice is not a desync");
    record_callee_instance(&mut records, &mut residual, true, record(1, 11, true));
    assert_eq!(records.len(), 2, "the conflicting record is kept for the edge decision");
    assert!(residual, "one id naming two definitions arms the tripwire");
    let sites = [SiteResolution::NotAnItemRecord; 2];
    assert!(matches!(decide_edge(true, &records, &sites), Err(EdgeRefusal::Conflicting(..))));
    let mut kinds = Vec::new();
    let mut kind_residual = false;
    record_callee_instance(&mut kinds, &mut kind_residual, true, record(2, 10, true));
    record_callee_instance(&mut kinds, &mut kind_residual, true, record(2, 10, false));
    assert!(kind_residual, "one id naming an item and a shim is a desync too");
    assert_eq!(kinds.len(), 2);
}

fn item(def_index: u32) -> ty::Instance<'static> {
    ty::Instance { def: ty::InstanceKind::Item(def(def_index)), args: ty::GenericArgs::empty() }
}

/// THE RE-DERIVATION'S DECISION, negatively. A site that resolves to exactly the recorded pair
/// admits it; a site resolving to ANOTHER item (a lowering that linked a same-signature item),
/// to a NON-item (an intrinsic the free-fn fast path recorded as an item), or not at all is
/// refused; a concretely keyed edge the lowering never recorded is refused; an edge with nothing
/// recorded and no concrete key, or a shim-kind record, links nothing.
#[test]
fn an_edge_is_admitted_only_as_the_pair_its_site_resolves_to() {
    let linked = record(1, 10, true);
    // Exactly the recorded pair.
    assert_eq!(
        decide_edge(true, &[linked], &[SiteResolution::Resolved(item(10))]),
        Ok(Some(linked))
    );
    // Another item with the same signature.
    assert_eq!(
        decide_edge(true, &[linked], &[SiteResolution::Resolved(item(11))]),
        Err(EdgeRefusal::Misresolved(linked, item(11)))
    );
    // A non-item: an intrinsic.
    let intrinsic =
        ty::Instance { def: ty::InstanceKind::Intrinsic(def(10)), args: ty::GenericArgs::empty() };
    assert_eq!(
        decide_edge(true, &[linked], &[SiteResolution::Resolved(intrinsic)]),
        Err(EdgeRefusal::NotAnItem(linked, intrinsic))
    );
    // Unresolvable.
    assert_eq!(
        decide_edge(true, &[linked], &[SiteResolution::Unresolvable("no")]),
        Err(EdgeRefusal::Unresolvable(linked, "no"))
    );
    // One good site does not excuse a bad one.
    let second_site = CalleeInstanceRecord { site_def: def(12), ..linked };
    assert_eq!(
        decide_edge(
            true,
            &[linked, second_site],
            &[SiteResolution::Resolved(item(10)), SiteResolution::Resolved(item(13))]
        ),
        Err(EdgeRefusal::Misresolved(second_site, item(13)))
    );
    // Never recorded.
    assert_eq!(decide_edge(true, &[], &[]), Err(EdgeRefusal::Unrecorded));
    assert_eq!(decide_edge(false, &[], &[]), Ok(None), "a havoc edge links nothing");
    // A shim-kind record links nothing (the assembler refuses the edge).
    let shim = record(1, 10, false);
    assert_eq!(decide_edge(true, &[shim], &[SiteResolution::NotAnItemRecord]), Ok(None));
    // An item record whose site was not re-derived, or a missing site, is refused.
    assert!(matches!(
        decide_edge(true, &[linked], &[SiteResolution::NotAnItemRecord]),
        Err(EdgeRefusal::Unresolvable(..))
    ));
    assert!(matches!(decide_edge(true, &[linked], &[]), Err(EdgeRefusal::Unresolvable(..))));
}

fn hex(text: &str) -> String {
    text.bytes().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn a_declaration_name_is_matched_by_path_definition_and_concrete_key() {
    let (path, definition, concrete) = ("pick", "00aa11bb", "0102");
    // The bare display path: the ONE declaration of that definition in the module.
    assert_eq!(declaration_name_matches("pick", path, definition, concrete), Ok(()));
    // The collision form, checked in full.
    let key = hex("havoc:pick|concrete-v1:0102");
    let full = format!("!trust_bodyless_instance::pick::00aa11bb-{key}");
    assert_eq!(declaration_name_matches(&full, path, definition, concrete), Ok(()));
    // Another instance of the same definition (pick::<u16> for pick::<u8>).
    assert!(declaration_name_matches(&full, path, definition, "0103").is_err());
    // Another definition with the same path.
    let other_def = format!("!trust_bodyless_instance::pick::00aa11bc-{key}");
    assert!(declaration_name_matches(&other_def, path, definition, concrete).is_err());
    // Another path.
    assert!(declaration_name_matches("tag", path, definition, concrete).is_err());
    assert!(declaration_name_matches(&full, "pic", definition, concrete).is_err());
    // A key with no class, and undecodable hex.
    let classless =
        format!("!trust_bodyless_instance::pick::00aa11bb-{}", hex(":pick|concrete-v1:0102"));
    assert!(declaration_name_matches(&classless, path, definition, concrete).is_err());
    assert!(
        declaration_name_matches(
            "!trust_bodyless_instance::pick::00aa11bb-zz",
            path,
            definition,
            concrete
        )
        .is_err()
    );
    // The reserved unresolved / conflict names never match.
    assert!(declaration_name_matches("!unknown_callee_3", path, definition, concrete).is_err());
}

/// `AssembledCrateModuleForCodegen::exact_instance_body` answers only a monomorphic local plain
/// item; every other shape is `NotMonomorphicLocalItem`.
#[test]
fn only_a_monomorphic_local_item_has_a_handoff_body() {
    assert!(is_monomorphic_local_item(true, true, true));
    assert!(!is_monomorphic_local_item(true, true, false), "a type or const argument");
    assert!(!is_monomorphic_local_item(true, false, true), "an upstream item");
    assert!(!is_monomorphic_local_item(false, true, true), "a shim");
}

// ------------------------------------------------------------------ placeholders the module shows

fn one_block_function(body: Vec<Inst>) -> Function {
    let mut module = trust_ir::Module::new("undef_scan");
    let ty = module
        .add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "scan", ty, BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    for inst in body {
        block.body.push(trust_ir::InstrNode::new(inst));
    }
    f.blocks.push(block);
    f
}

/// An `undef` anywhere in a body is a placeholder for a value the producer did not model (the
/// whole-value store of a non-plain value stores `undef <lane ty>`; a variant test on an opaque
/// value is `undef bool`), and the gate's fact and the assembler's leaf check both read this scan.
#[test]
fn an_undef_anywhere_in_a_body_is_a_placeholder() {
    let ret = |v: u32| Inst::Return { values: vec![trust_ir::ValueId::new(v)] };
    let constant = Inst::Const { ty: Ty::Bool, value: trust_ir::Constant::Bool(true) };
    assert!(!function_has_undef_placeholder(&one_block_function(vec![constant, ret(0)])));
    let havoc = Inst::Undef { ty: Ty::Bool };
    assert!(function_has_undef_placeholder(&one_block_function(vec![havoc, ret(0)])));
}
