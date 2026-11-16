//! The trust-ir lane on authored modules: level 1 (one body's walk, as facts), level 2 (the
//! crate graph the engine solves), the foreign world, and the differential's classification.
//! No `TyCtxt`: the classifier's input is stated directly.

use std::collections::BTreeMap;

use trust_ir::function_dependencies::Verdict;
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, FuncTyId, Function, Global, Inst,
    InstrNode, Linkage, Module, Ty, ValueId, Visibility,
};

use super::*;

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn ret() -> InstrNode {
    node(Inst::Return { values: vec![] })
}

fn call(callee: u32) -> InstrNode {
    node(Inst::Call { callee: FuncId::new(callee), args: vec![] })
}

fn reify(function: u32, result: u32) -> InstrNode {
    node(Inst::Const {
        ty: Ty::Func(FuncTyId::new(0)),
        value: Constant::FnDef(FuncId::new(function)),
    })
    .with_result(ValueId::new(result))
}

/// An indirect call through `%0`, the body's `fn()` parameter: no static analysis resolves it.
fn call_through_parameter() -> InstrNode {
    node(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: FuncTyId::new(0),
        args: vec![],
        calling_conv: CallingConv::Rust,
    })
}

fn function(id: u32, nodes: Vec<InstrNode>) -> Function {
    let mut function = Function::new(FuncId::new(id), "body", FuncTyId::new(0), BlockId::new(0));
    let mut block =
        Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Func(FuncTyId::new(0)));
    block.body = nodes;
    function.blocks.push(block);
    function
}

/// `fn()` is signature 0 and `fn(u32)` signature 1; the body is `functions[0]`, taking one
/// value `%0` (a fn pointer, for the indirect-call cases).
fn body(nodes: Vec<InstrNode>) -> Module {
    let mut module = Module::new("authored_spawn_census_body");
    module.func_types.push(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None });
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![],
        is_vararg: false,
        abi: None,
    });
    module.functions.push(function(0, nodes));
    module
}

fn global(initializer: Option<Constant>) -> Global {
    Global {
        name: "G".into(),
        ty: Ty::Ptr,
        mutable: true,
        initializer,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn row(id: u32, class: CalleeClass<u32>) -> Declaration<'static, u32> {
    Declaration { func_id: FuncId::new(id), class, params: None, returns_memory: false }
}

/// A foreign declaration signed with no parameter: a call of it hands foreign code nothing.
fn nullary_foreign(id: u32) -> Declaration<'static, u32> {
    Declaration {
        func_id: FuncId::new(id),
        class: CalleeClass::Foreign,
        params: Some(&[]),
        returns_memory: false,
    }
}

/// A body that calls foreign code and hands it nothing.
fn calls_c() -> BodyFacts<u32> {
    walk_body(&body(vec![call(1), ret()]), &[nullary_foreign(1)], &[])
}

fn gaps(gaps: &[Gap]) -> GapSet {
    let mut set = GapSet::default();
    for gap in gaps {
        set.insert(*gap);
    }
    set
}

fn walked(module: &Module, rows: &[Declaration<'_, u32>]) -> BodyGraph<u32> {
    match walk_body(module, rows, &[]) {
        BodyFacts::Walked(graph) => graph,
        BodyFacts::Declined(gap) => panic!("the walk declined the body: {gap:?}"),
    }
}

/// The crate graph of `bodies`, answered as (verdict, gaps) per body.
fn solve(
    bodies: Vec<(u32, BodyFacts<u32>)>,
    world: &ForeignWorld<u32>,
) -> BTreeMap<u32, (Verdict, GapSet)> {
    solve_crate(&bodies, world)
        .into_iter()
        .map(|(body, answer)| (body, (answer.verdict, answer.gaps)))
        .collect()
}

/// One body alone in its crate.
fn alone(module: &Module, rows: &[Declaration<'_, u32>]) -> (Verdict, GapSet) {
    solve(vec![(1, walk_body(module, rows, &[]))], &ForeignWorld::default())[&1]
}

#[test]
fn a_seed_call_spawns_and_a_seed_value_escapes() {
    let module = body(vec![call(1), ret()]);
    assert_eq!(alone(&module, &[row(1, CalleeClass::Seed)]), (Verdict::Spawns, GapSet::default()));
    let module = body(vec![reify(1, 1), ret()]);
    assert_eq!(alone(&module, &[row(1, CalleeClass::Seed)]), (Verdict::Escapes, GapSet::default()));
}

/// A port is the named body's own node: a call of it is a RUN edge into that body, a value of
/// it a CREATE edge, a body named twice is one node, and a recursion alone runs nothing.
#[test]
fn a_port_is_the_named_bodys_node() {
    let spawner = walk_body(&body(vec![call(1), ret()]), &[row(1, CalleeClass::Seed)], &[]);
    let caller = walk_body(
        &body(vec![call(1), call(2), ret()]),
        &[row(1, CalleeClass::Body(7)), row(2, CalleeClass::Body(7))],
        &[],
    );
    let namer = walk_body(&body(vec![reify(2, 1), ret()]), &[row(2, CalleeClass::Body(7))], &[]);
    let recursion = walk_body(&body(vec![call(1), ret()]), &[row(1, CalleeClass::Body(9))], &[]);
    let lane = solve(
        vec![(7, spawner), (8, caller), (6, namer), (9, recursion)],
        &ForeignWorld::default(),
    );
    assert_eq!(lane[&7], (Verdict::Spawns, GapSet::default()));
    assert_eq!(lane[&8], (Verdict::Spawns, GapSet::default()));
    assert_eq!(lane[&6], (Verdict::Escapes, GapSet::default()));
    assert_eq!(lane[&9], (Verdict::Quiet, GapSet::default()));
}

#[test]
fn absent_is_never_quiet() {
    // Every row with no body here, an unledgered id, a drop, and each runtime service.
    let module = body(vec![
        call(1),
        call(2),
        call(3),
        call(4),
        call(5),
        call(99),
        node(Inst::Drop { ty: Ty::U8, ptr: ValueId::new(0) }),
        node(Inst::Assert {
            cond: ValueId::new(0),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        }),
        ret(),
    ]);
    let rows = [
        row(1, CalleeClass::Gap(Gap::Havoc)),
        row(2, CalleeClass::Gap(Gap::GenericInstance)),
        row(3, CalleeClass::Gap(Gap::ExternRust)),
        row(4, CalleeClass::Gap(Gap::UnwindingForeign)),
        row(5, CalleeClass::Gap(Gap::OutsideCensus)),
    ];
    let expected = gaps(&[
        Gap::Havoc,
        Gap::GenericInstance,
        Gap::ExternRust,
        Gap::UnwindingForeign,
        Gap::OutsideCensus,
        Gap::UnledgeredCallee,
        Gap::Drop,
        Gap::Panic,
    ]);
    assert_eq!(alone(&module, &rows), (Verdict::Unknown, expected));
    // Each such reach is code this lane cannot see, which may hand foreign code anything.
    assert!(walked(&module, &rows).hands_out);
}

#[test]
fn the_producer_omissions_are_gaps() {
    let module = body(vec![ret()]);
    let omissions = [
        TrustIrOmission::ElidedDrops("live temporary".to_string()),
        TrustIrOmission::ClosureValueAsUnit,
        TrustIrOmission::PendingConstValue,
    ];
    let facts = walk_body::<u32>(&module, &[], &omissions);
    let lane = solve(vec![(1, facts)], &ForeignWorld::default());
    assert_eq!(
        lane[&1],
        (Verdict::Unknown, gaps(&[Gap::ElidedDrops, Gap::ClosureValueOmitted, Gap::PendingConst]))
    );
    assert_eq!(alone(&module, &[]), (Verdict::Quiet, GapSet::default()));
    assert!(!walked(&module, &[]).hands_out);
}

/// The other bodies' callables are not in a body's module, so its pools are never closed: an
/// indirect call with no callable of its shape in the body is UNKNOWN, never QUIET (one
/// module per body would otherwise close an empty pool).
#[test]
fn an_indirect_call_is_unknown_when_its_pool_is_not_the_crates() {
    let module = body(vec![call_through_parameter(), ret()]);
    assert_eq!(alone(&module, &[]), (Verdict::Unknown, gaps(&[Gap::IndirectCall])));
    // Its target may be foreign code, which may keep what it is handed.
    assert!(walked(&module, &[]).hands_out);
}

/// An APPROX edge the engine derived in a body's walk is derived again in the crate graph, from
/// a one-member pool, and the crate graph's solve labels it: here an adapter the body runs
/// calls through a pool that holds a port, which another adapter the body never runs made
/// into a value. The path's weakest edge is that APPROX edge: INDIRECT, by the engine's
/// labelling of the crate graph (a defect, an adapter's own APPROX edge, would refuse every
/// body as `census-fallback` instead).
#[test]
fn a_derived_approx_edge_is_derived_again_and_labelled_by_the_engine() {
    let mut module = body(vec![call(5), ret()]);
    module.functions.push(function(5, vec![call_through_parameter(), ret()]));
    module.functions.push(function(6, vec![reify(1, 1), ret()]));
    let caller = walk_body(&module, &[row(1, CalleeClass::Body(2))], &[]);
    let spawner = walk_body(&body(vec![call(1), ret()]), &[row(1, CalleeClass::Seed)], &[]);
    let lane = solve(vec![(1, caller), (2, spawner)], &ForeignWorld::default());
    assert_eq!(lane[&1], (Verdict::Indirect, gaps(&[Gap::IndirectCall])));
    assert_eq!(lane[&2], (Verdict::Spawns, GapSet::default()));
}

/// Rule H: foreign code handed only data is quiet; unsigned, it may be handed anything. Either
/// way the body reaches the foreign world, and an operand handed out may be kept.
#[test]
fn foreign_code_is_charged_by_what_it_is_handed() {
    let with_operand = node(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] });
    let module = body(vec![with_operand, ret()]);
    let signed: &[Ty] = &[Ty::U32];
    let rows = [Declaration {
        func_id: FuncId::new(1),
        class: CalleeClass::Foreign,
        params: Some(signed),
        returns_memory: false,
    }];
    let graph = walked(&module, &rows);
    assert!(graph.hands_out && graph.nodes.contains(&Role::Foreign));
    // It hands out, so the world may call back what it kept: UNKNOWN.
    assert_eq!(alone(&module, &rows), (Verdict::Unknown, gaps(&[Gap::ForeignCallback])));
    let unsigned = [row(1, CalleeClass::Foreign)];
    assert!(alone(&module, &unsigned).1.contains(Gap::IndirectCall));
    // A call that hands foreign code nothing keeps nothing.
    let module = body(vec![call(1), ret()]);
    assert!(!walked(&module, &rows).hands_out);
    assert_eq!(alone(&module, &rows), (Verdict::Quiet, GapSet::default()));
    // Unless what it returns may lead to memory foreign code reads later: a store through it
    // is a hand-out.
    let returning = [Declaration { returns_memory: true, ..rows[0].clone() }];
    assert!(walked(&module, &returning).hands_out);
    assert_eq!(alone(&module, &returning), (Verdict::Unknown, gaps(&[Gap::ForeignCallback])));
}

/// Code out of sight may have handed foreign code a callable it keeps, or stored one where
/// foreign code reads it: a body this lane does not walk (unless Clean-origin, R5), another
/// crate's Rust called with no argument at all, a global whose contents the module does not
/// hold (an `extern` static). Then a body that calls foreign code with nothing is UNKNOWN.
#[test]
fn hand_outs_out_of_sight_open_the_foreign_world() {
    let kept = (Verdict::Unknown, gaps(&[Gap::ForeignCallback]));
    for gap in [Gap::Declined(TrustIrDecline::Unsupported), Gap::NotConserved, Gap::Abstracted] {
        let lane =
            solve(vec![(1, calls_c()), (2, BodyFacts::Declined(gap))], &ForeignWorld::default());
        assert_eq!(lane[&1], kept, "{gap:?}");
    }
    let lane = solve(
        vec![(1, calls_c()), (2, BodyFacts::Declined(Gap::CleanOrigin))],
        &ForeignWorld::default(),
    );
    assert_eq!(lane[&1], (Verdict::Quiet, GapSet::default()));
    // Another crate's Rust, called with no argument: it may register its own callables.
    let extern_rust = [row(1, CalleeClass::Gap(Gap::ExternRust))];
    let calls_dep = walk_body(&body(vec![call(1), ret()]), &extern_rust, &[]);
    let lane = solve(vec![(1, calls_c()), (2, calls_dep)], &ForeignWorld::default());
    assert_eq!(lane[&1], kept);
    // A store into a global the module has no contents for may hand foreign code a callable;
    // a global the module holds is the crate's own memory.
    let touches = |initializer| {
        let mut module = body(vec![node(Inst::GlobalAddr { global: GlobalId::new(0) }), ret()]);
        module.globals.push(global(initializer));
        walked(&module, &[]).hands_out
    };
    assert!(touches(None));
    assert!(!touches(Some(Constant::Int(0))));
}

/// Foreign code may call what the crate graph exports by symbol (INDIRECT, never a spawn
/// claim), and read what it exports as a static, and call back kept callbacks (not
/// enumerated: UNKNOWN).
#[test]
fn the_foreign_world_reaches_the_exports() {
    let spawner = || walk_body(&body(vec![call(1), ret()]), &[row(1, CalleeClass::Seed)], &[]);
    let world = ForeignWorld { exported: vec![2], gaps: GapSet::default() };
    let lane = solve(vec![(1, calls_c()), (2, spawner())], &world);
    assert_eq!(lane[&1].0, Verdict::Indirect);
    let lane = solve(vec![(1, calls_c()), (2, spawner())], &ForeignWorld::default());
    assert_eq!(lane[&1], (Verdict::Quiet, GapSet::default()));
    let world =
        ForeignWorld { exported: vec![99], gaps: gaps(&[Gap::GlobalAsm, Gap::ExportedStatic]) };
    let lane = solve(vec![(1, calls_c())], &world);
    assert_eq!(
        lane[&1],
        (Verdict::Unknown, gaps(&[Gap::ExportedStatic, Gap::OutsideCensus, Gap::GlobalAsm]))
    );
}

/// Two rows under one id, or a row under the body's own id, are one ambiguous node: the walk
/// reads none of their classes.
#[test]
fn an_id_two_rows_share_is_unknown() {
    let module = body(vec![call(1), ret()]);
    let rows = [row(1, CalleeClass::Body(7)), row(1, CalleeClass::Seed)];
    assert_eq!(alone(&module, &rows), (Verdict::Unknown, gaps(&[Gap::Malformed])));
    let rows = [row(0, CalleeClass::Seed)];
    assert_eq!(alone(&module, &rows), (Verdict::Unknown, gaps(&[Gap::Malformed])));
}

#[test]
fn the_crate_graph_composes_the_walks() {
    let calls =
        |target| walk_body(&body(vec![call(1), ret()]), &[row(1, CalleeClass::Body(target))], &[]);
    let panics_and_spawns = walk_body(
        &body(vec![
            node(Inst::Assert {
                cond: ValueId::new(0),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
            call(1),
            ret(),
        ]),
        &[row(1, CalleeClass::Seed)],
        &[],
    );
    let bodies = vec![
        (1, calls(2)),
        (2, panics_and_spawns),
        (5, BodyFacts::Declined(Gap::Declined(TrustIrDecline::Unsupported))),
        (6, calls(5)),
        (7, walk_body(&body(vec![ret()]), &[], &[])),
        (8, calls(99)),
    ];
    let lane = solve(bodies, &ForeignWorld::default());
    let panic = gaps(&[Gap::Panic]);
    assert_eq!(lane[&1], (Verdict::Spawns, panic));
    assert_eq!(lane[&2], (Verdict::Spawns, panic));
    let declined = gaps(&[Gap::Declined(TrustIrDecline::Unsupported)]);
    assert_eq!(lane[&5], (Verdict::Unknown, declined));
    assert_eq!(lane[&6], (Verdict::Unknown, declined));
    assert_eq!(lane[&7], (Verdict::Quiet, GapSet::default()));
    assert_eq!(lane[&8], (Verdict::Unknown, gaps(&[Gap::OutsideCensus])));
}

#[test]
fn the_differential_names_both_invariants() {
    use Agreement as A;
    use Verdict as V;
    assert_eq!(A::compare(V::Spawns, true, V::Spawns), A::Equal);
    assert_eq!(A::compare(V::Quiet, true, V::Quiet), A::Equal);
    assert_eq!(A::compare(V::Spawns, true, V::Unknown), A::TrustIrUnknown);
    assert_eq!(A::compare(V::Quiet, true, V::Unknown), A::TrustIrUnknown);
    assert_eq!(A::compare(V::Spawns, true, V::Indirect), A::Differs);
    assert_eq!(A::compare(V::Unknown, true, V::Escapes), A::Differs);
    for mir in [V::Unknown, V::Indirect, V::Escapes, V::Spawns] {
        assert_eq!(A::compare(mir, true, V::Quiet), A::FailOpen);
        assert!(A::FailOpen.is_violation());
    }
    for trust_ir in [V::Indirect, V::Escapes, V::Spawns] {
        assert_eq!(A::compare(V::Quiet, true, trust_ir), A::MirQuietClaim);
    }
    assert!(A::MirQuietClaim.is_violation());
    assert_eq!(A::compare(V::Quiet, false, V::Spawns), A::MirNotWalked);
    assert!(!A::MirNotWalked.is_violation() && !A::TrustIrUnknown.is_violation());
    assert!(!A::MirFellBack.is_violation());
}

#[test]
fn every_gap_has_its_own_bit_and_spelling() {
    let mut spellings = std::collections::BTreeSet::new();
    let mut bits = 0u64;
    for gap in Gap::ALL {
        assert!(spellings.insert(gap.as_str()), "{gap:?} shares a spelling");
        assert_eq!(bits & gap.bit(), 0, "{gap:?} shares a bit");
        bits |= gap.bit();
    }
    assert!(Gap::ALL.len() <= 64, "a GapSet is one u64");
    // A declined body is reported in the query's own spelling, for every decline.
    for decline in TrustIrDecline::ALL {
        assert!(Gap::ALL.contains(&Gap::Declined(decline)));
        assert_eq!(Gap::Declined(decline).as_str(), decline.as_str());
    }
}
