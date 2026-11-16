//! Source identities for the already admitted constant-reification call shape.
//!
//! These facts do not change the extracted function or the native producer. They
//! let the existing call gates ask the unconditional proof registry about the
//! exact source target. An identity is not a proof of that target.

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{self, Body, Location, Operand, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{FxHashMap, compiler_function_source_digest_hex};

#[derive(Clone, Debug, PartialEq, Eq)]
struct BoundCall {
    location: Location,
    definition: Location,
    target: DefId,
    original_mir: Fingerprint,
    signature: Fingerprint,
    identity: trust_types::CalleeIdentity,
    // The original portable call includes the pointer operand, all arguments,
    // destination, normal/unwind edges, safety and complete portable signature.
    // Full rustc signature equality is checked separately during capture.
    original_call: Vec<u8>,
}

/// Invocation-local, owner-bound facts. No deserializer or public constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Bindings {
    owner: DefId,
    source_digest: String,
    calls: FxHashMap<trust_types::BlockId, BoundCall>,
}

impl Bindings {
    pub(super) fn identities(
        &self,
        owner: DefId,
        func: &trust_types::VerifiableFunction,
    ) -> FxHashMap<trust_types::BlockId, trust_types::CalleeIdentity> {
        let mut identities = FxHashMap::default();
        if self.owner != owner
            || compiler_function_source_digest_hex(func).ok().as_ref() != Some(&self.source_digest)
        {
            return identities;
        }
        for block in &func.body.blocks {
            let Some(bound) = self.calls.get(&block.id) else { continue };
            if serde_json::to_vec(&block.terminator).ok().as_ref() == Some(&bound.original_call) {
                identities.insert(block.id, bound.identity);
            }
        }
        identities
    }
}

/// All writes, including terminator outputs, pass through the MIR visitor.
/// Only the one whole reification store is allowed; every address escape,
/// projection mutation, asm output, call/yield output and drop refuses binding.
struct PinnedLocal {
    local: mir::Local,
    definition: Location,
    valid: bool,
}

impl<'tcx> Visitor<'tcx> for PinnedLocal {
    fn visit_local(&mut self, local: mir::Local, context: PlaceContext, location: Location) {
        if local != self.local {
            return;
        }
        self.valid &= match context {
            PlaceContext::MutatingUse(MutatingUseContext::Store) => location == self.definition,
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::Copy
                | NonMutatingUseContext::Move
                | NonMutatingUseContext::Inspect
                | NonMutatingUseContext::PlaceMention,
            )
            | PlaceContext::NonUse(_) => true,
            _ => false,
        };
    }
}

/// Stronger than counting explicit assignments: the sole definition must
/// dominate the call, so a formal parameter's entry value or another CFG arm
/// cannot reach it. The visitor audits writes the old assignment scan omitted.
fn dominating_reification<'a, 'tcx>(
    body: &'a Body<'tcx>,
    callee: &Operand<'tcx>,
    call: Location,
) -> Option<(Location, &'a mir::ConstOperand<'tcx>)> {
    let constant = super::sole_reified_constant_of_callee(body, callee)?;
    let (Operand::Copy(place) | Operand::Move(place)) = callee else { return None };
    let mut definition = None;
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(assignment) = &statement.kind
                && assignment.0.local == place.local
            {
                if !assignment.0.projection.is_empty() || definition.is_some() {
                    return None;
                }
                definition = Some(Location { block: bb, statement_index });
            }
        }
    }
    let definition = definition?;
    pinned_definition_dominates(body, place.local, definition, call)
        .then_some((definition, constant))
}

fn pinned_definition_dominates(
    body: &Body<'_>,
    local: mir::Local,
    definition: Location,
    call: Location,
) -> bool {
    let dominators = body.basic_blocks.dominators();
    if !dominators.is_reachable(call.block)
        || !dominators.dominates(definition.block, call.block)
        || (definition.block == call.block && definition.statement_index >= call.statement_index)
    {
        return false;
    }
    let mut pinned = PinnedLocal { local, definition, valid: true };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        pinned.visit_basic_block_data(bb, data);
    }
    pinned.valid
}

pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &trust_types::VerifiableFunction,
) -> Option<Bindings> {
    let owner = super::zero_obligation_source_owner(body.source)?;
    let mut calls = FxHashMap::default();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else { continue };
        let TerminatorKind::Call { func: callee, .. } = &term.kind else { continue };
        let location = Location { block: bb, statement_index: data.statements.len() };
        let Some((definition, constant)) = dominating_reification(body, callee, location) else {
            continue;
        };
        // Preserve EVERY previous local/body/requires/generic/type-argument guard.
        if !super::indirect_callee_is_a_reified_constant(tcx, body, callee) {
            continue;
        }
        let ty::FnDef(target, args) = *constant.const_.ty().kind() else { continue };
        let args = args.skip_binder();
        let pointer_ty = callee.ty(&body.local_decls, tcx);
        if !matches!(pointer_ty.kind(), ty::FnPtr(..)) {
            continue;
        }
        // Compare full rustc signatures, including ABI, safety and variadicness;
        // the portable FnPtr type alone does not carry all of those fields.
        // `Ty::fn_sig` already removes its Unnormalized API wrapper. Do the
        // same for the item signature, retaining the full Binder for exact
        // comparison; normalization must not supply an additional admission.
        let target_sig = tcx.erase_and_anonymize_regions(
            tcx.fn_sig(target).instantiate(tcx, args).skip_normalization(),
        );
        if target_sig != tcx.erase_and_anonymize_regions(pointer_ty.fn_sig(tcx)) {
            continue;
        }
        let (original_mir, signature) = tcx.with_stable_hashing_context(|mut hcx| {
            let mut source = StableHasher::new();
            let mut signature = StableHasher::new();
            hcx.while_hashing_spans(true, |hcx| {
                term.stable_hash(hcx, &mut source);
                target_sig.stable_hash(hcx, &mut signature);
            });
            (source.finish(), signature.finish())
        });
        let Some(identity) = trust_mir_extract::instance_identity(tcx, target, args) else {
            continue;
        };
        let id = trust_types::BlockId(bb.as_usize());
        let mut matching = func.body.blocks.iter().filter(|block| block.id == id);
        let Some(block) = matching.next() else { continue };
        if matching.next().is_some() {
            return None;
        }
        let trust_types::Terminator::Call { func: key, callee_identity, .. } = &block.terminator
        else {
            continue;
        };
        if key != trust_types::TRUST_INDIRECT_CALLEE_PATH || callee_identity.is_some() {
            continue;
        }
        calls.insert(
            id,
            BoundCall {
                location,
                definition,
                target,
                original_mir,
                signature,
                identity,
                original_call: serde_json::to_vec(&block.terminator).ok()?,
            },
        );
    }
    Some(Bindings { owner, source_digest: compiler_function_source_digest_hex(func).ok()?, calls })
}

/// Ordering only: no producer body expansion and no proof authority. This runs
/// before MIR is stolen, without forcing target verification or requires queries.
pub(super) fn ordering_callees<'tcx>(body: &Body<'tcx>) -> Vec<LocalDefId> {
    let mut callees = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else { continue };
        let TerminatorKind::Call { func, .. } = &term.kind else { continue };
        let location = Location { block: bb, statement_index: data.statements.len() };
        if let Some((_, constant)) = dominating_reification(body, func, location)
            && let ty::FnDef(target, _) = *constant.const_.ty().kind()
            && let Some(target) = target.as_local()
        {
            callees.push(target);
        }
    }
    callees
}

#[cfg(test)]
mod tests {
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
}
