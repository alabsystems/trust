use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Place, Rvalue, SourceInfo, Statement, Terminator, WithRetag,
};

#[test]
fn identities_are_bound_to_the_owner_and_entire_original_source() {
    use trust_types::{BlockId, CalleeIdentity, SourceSpan, Ty, UnwindEdge};
    let owner = rustc_span::def_id::CRATE_DEF_ID.to_def_id();
    let identity = CalleeIdentity { stable_crate_id: 17, def_index: 1, substs_digest: [2, 3] };
    let call = trust_types::Terminator::Call {
        func: trust_types::TRUST_INDIRECT_CALLEE_PATH.into(),
        args: vec![trust_types::Operand::Copy(trust_types::Place::local(1))],
        dest: trust_types::Place::local(0),
        target: Some(BlockId(1)),
        unwind: UnwindEdge::Continue,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
    };
    let func = trust_types::VerifiableFunction {
        name: "caller".into(),
        def_path: "test::caller".into(),
        span: SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: vec![trust_types::LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![trust_types::BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call.clone(),
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let bindings = Bindings {
        owner,
        source_digest: compiler_function_source_digest_hex(&func).unwrap(),
        calls: [(
            BlockId(0),
            BoundCall {
                location: Location { block: mir::START_BLOCK, statement_index: 0 },
                definition: Location { block: mir::START_BLOCK, statement_index: 0 },
                target: owner,
                original_mir: Fingerprint::ZERO,
                signature: Fingerprint::ZERO,
                identity,
                original_call: serde_json::to_vec(&call).unwrap(),
            },
        )]
        .into_iter()
        .collect(),
    };
    assert_eq!(bindings.identities(owner, &func).get(&BlockId(0)), Some(&identity));
    // Source identity is not evidence: the production gate still needs
    // this exact callee's entry in the unconditional proof registry.
    let bound = bindings.identities(owner, &func);
    let empty = super::super::FxHashSet::default();
    let no_proven_targets = super::super::FxHashSet::default();
    let exact_proven_target = [identity].into_iter().collect();
    let other_proven_target =
        [CalleeIdentity { def_index: identity.def_index + 1, ..identity }]
            .into_iter()
            .collect();
    let ask = |proven_identities| {
        super::super::all_calls_registry_or_bridge_total_with_bindings(
            &bound,
            &empty,
            proven_identities,
            &empty,
            &empty,
            &empty,
            &empty,
            &empty,
            &empty,
            &func,
        )
    };
    assert!(!ask(&no_proven_targets));
    assert!(ask(&exact_proven_target));
    assert!(!ask(&other_proven_target));
    let mut changed_owner = owner;
    changed_owner.index = rustc_span::def_id::DefIndex::from_usize(1);
    assert!(bindings.identities(changed_owner, &func).is_empty());
    for change in 0..7 {
        let mut changed = func.clone();
        let trust_types::Terminator::Call { args, dest, target, unwind, span, .. } =
            &mut changed.body.blocks[0].terminator
        else {
            unreachable!()
        };
        match change {
            0 => args.push(trust_types::Operand::Copy(trust_types::Place::local(2))),
            1 => *dest = trust_types::Place::local(2),
            2 => *target = Some(BlockId(2)),
            3 => *unwind = UnwindEdge::Cleanup(BlockId(2)),
            4 => span.line_start += 1,
            5 => changed.body.locals[0].ty = Ty::i32(),
            6 => changed.def_path.push_str("_another_source"),
            _ => unreachable!(),
        }
        assert!(bindings.identities(owner, &changed).is_empty(), "source mutation {change}");
    }
}

use super::*;

#[test]
fn every_other_write_or_address_escape_withdraws_the_binding() {
    let local = mir::Local::from_usize(1);
    let definition = Location { block: mir::START_BLOCK, statement_index: 0 };
    for context in [
        PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant),
        PlaceContext::MutatingUse(MutatingUseContext::AsmOutput),
        PlaceContext::MutatingUse(MutatingUseContext::Call),
        PlaceContext::MutatingUse(MutatingUseContext::Yield),
        PlaceContext::MutatingUse(MutatingUseContext::Drop),
        PlaceContext::MutatingUse(MutatingUseContext::Borrow),
        PlaceContext::MutatingUse(MutatingUseContext::RawBorrow),
        PlaceContext::MutatingUse(MutatingUseContext::Projection),
        PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow),
        PlaceContext::NonMutatingUse(NonMutatingUseContext::FakeBorrow),
        PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow),
    ] {
        let mut pinned = PinnedLocal { local, definition, valid: true };
        pinned.visit_local(local, context, definition);
        assert!(!pinned.valid, "unaccounted write/escape: {context:?}");
    }
    let mut pinned = PinnedLocal { local, definition, valid: true };
    pinned.visit_local(local, PlaceContext::MutatingUse(MutatingUseContext::Store), definition);
    assert!(pinned.valid);
    pinned.visit_local(
        local,
        PlaceContext::MutatingUse(MutatingUseContext::Store),
        Location { statement_index: 1, ..definition },
    );
    assert!(!pinned.valid, "a second store must withdraw the first target");
}

#[test]
fn parameter_entry_and_non_dominating_assignments_do_not_bind() {
    let source_info = SourceInfo::outermost(rustc_span::DUMMY_SP);
    let block = |kind| BasicBlockData::new(Some(Terminator { source_info, kind }), false);
    let mut blocks = IndexVec::<BasicBlock, BasicBlockData<'static>>::from_raw(vec![
        block(TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from(mir::Local::from_usize(2))),
            targets: mir::SwitchTargets::new(
                [(0, BasicBlock::from_usize(1))].into_iter(),
                BasicBlock::from_usize(2),
            ),
        }),
        block(TerminatorKind::Goto {
            target: BasicBlock::from_usize(3),
            loop_hint_attrs: Default::default(),
        }),
        block(TerminatorKind::Goto {
            target: BasicBlock::from_usize(3),
            loop_hint_attrs: Default::default(),
        }),
        block(TerminatorKind::Return),
    ]);
    let local = mir::Local::from_usize(1);
    let assignment = Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(local),
            Rvalue::Use(Operand::Copy(Place::from(mir::Local::from_usize(4))), WithRetag::Yes),
        ))),
    );
    blocks[BasicBlock::from_usize(1)].statements.push(assignment.clone());
    let mut body = Body::new_cfg_only(blocks);
    // A formal pointer has a genuine entry value. A sole explicit write in
    // one arm does not replace that value on the other arm.
    body.arg_count = 1;
    let definition = Location { block: BasicBlock::from_usize(1), statement_index: 0 };
    let call = Location { block: BasicBlock::from_usize(3), statement_index: 0 };
    assert!(!pinned_definition_dominates(&body, local, definition, call));

    body.basic_blocks.as_mut()[BasicBlock::from_usize(1)].statements.clear();
    body.basic_blocks.as_mut()[mir::START_BLOCK].statements.push(assignment);
    let definition = Location { block: mir::START_BLOCK, statement_index: 0 };
    assert!(
        pinned_definition_dominates(&body, local, definition, call),
        "a genuine dominating overwrite binds even a formal pointer"
    );
    assert!(
        !pinned_definition_dominates(&body, local, definition, definition),
        "a call cannot consume the value before its store"
    );
}
