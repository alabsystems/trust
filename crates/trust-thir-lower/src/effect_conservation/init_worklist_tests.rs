//! Work scheduling may change; the original data-flow solution must not.

use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlockData, SourceInfo, Statement, SwitchTargets, Terminator, WithRetag,
};
use rustc_span::DUMMY_SP;

use super::*;

// The original init_at_entry worklist at 0d3582e406c9. Keep its scheduling
// independent from production: sharing a queue would hide scheduling defects.
fn original_init_at_entry(
    body: &Body<'_>,
    reachable: &[bool],
    no_return: &BTreeSet<BasicBlock>,
) -> Vec<Option<InitState>> {
    let n = body.basic_blocks.len();
    let mut entry: Vec<Option<InitState>> = vec![None; n];
    entry[mir::START_BLOCK.as_usize()] =
        Some(InitState { maybe_init: body.args_iter().collect(), moved_fields: BTreeSet::new() });
    let mut work = vec![mir::START_BLOCK];
    while let Some(bb) = work.pop() {
        if !reachable[bb.as_usize()] {
            continue;
        }
        let Some(mut state) = entry[bb.as_usize()].clone() else {
            continue;
        };
        let data = &body.basic_blocks[bb];
        for stmt in &data.statements {
            transfer_statement(&stmt.kind, &mut state);
        }
        let Some(term) = &data.terminator else {
            continue;
        };
        let succs = real_successors(body, bb, no_return);
        transfer_terminator(&term.kind, &mut state);
        for s in succs {
            if !reachable[s.as_usize()] {
                continue;
            }
            let slot = &mut entry[s.as_usize()];
            let grew = match slot {
                None => {
                    *slot = Some(state.clone());
                    true
                }
                Some(have) => have.join(&state),
            };
            if grew {
                work.push(s);
            }
        }
    }
    entry
}

fn cfg(edges: &[Vec<usize>], operations: &[u8]) -> Body<'static> {
    let source_info = SourceInfo::outermost(DUMMY_SP);
    let blocks = edges.iter().enumerate().map(|(i, successors)| {
        let kind = if successors.is_empty() {
            TerminatorKind::Return
        } else {
            // Repeated successors are intentional: the queue must coalesce
            // visits without dropping later joins from other predecessors.
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Local::from_u32(1).into()),
                targets: SwitchTargets::new(
                    successors[..successors.len() - 1]
                        .iter()
                        .enumerate()
                        .map(|(value, &target)| (value as u128, BasicBlock::from_usize(target))),
                    BasicBlock::from_usize(*successors.last().unwrap()),
                ),
            }
        };
        let mut block = BasicBlockData::new(Some(Terminator { source_info, kind }), false);
        let op = operations[i];
        if op & 1 != 0 {
            block
                .statements
                .push(Statement::new(source_info, StatementKind::StorageDead(Local::from_u32(1))));
        }
        if op & 2 != 0 {
            block.statements.push(Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Local::from_u32(2).into(),
                    Rvalue::Use(Operand::Move(Local::from_u32(1).into()), WithRetag::No),
                ))),
            ));
        }
        block
    });
    // rustc's explicitly test-only CFG constructor does not need local types:
    // this analysis reads local identities and never queries their types.
    let mut body = Body::new_cfg_only(IndexVec::from_iter(blocks));
    body.arg_count = 1;
    body
}

fn assert_same(body: &Body<'_>, reachable: &[bool], no_return: &BTreeSet<BasicBlock>) {
    assert_eq!(
        init_at_entry(body, reachable, no_return),
        original_init_at_entry(body, reachable, no_return),
    );
}

#[test]
fn every_three_block_graph_keeps_the_original_fixed_point() {
    // Exhaust all directed edges, including self-loops and irreducible cycles,
    // and every assignment/kill combination. Unreachable blocks must stay None.
    for edge_bits in 0u16..512 {
        let edges: Vec<Vec<usize>> = (0..3)
            .map(|from| (0..3).filter(|to| edge_bits & (1 << (from * 3 + to)) != 0).collect())
            .collect();
        for operations in 0u8..64 {
            let body = cfg(&edges, &[operations & 3, (operations >> 2) & 3, operations >> 4]);
            let no_return = BTreeSet::new();
            assert_same(&body, &mir_reachable(&body, &no_return), &no_return);
        }
    }
}

#[test]
fn pending_join_and_backedge_updates_reach_the_downstream_block() {
    let body = cfg(&[vec![1, 2], vec![3], vec![1, 3], vec![1, 4], vec![]], &[0, 0, 2, 1, 0]);
    let no_return = BTreeSet::new();
    let reachable = mir_reachable(&body, &no_return);
    assert_same(&body, &reachable, &no_return);
    let entry = init_at_entry(&body, &reachable, &no_return);
    assert_eq!(entry[4].as_ref().unwrap().maybe_init, BTreeSet::from([Local::from_u32(2)]));
}

#[test]
fn repeated_edges_and_cleanup_blocks_keep_the_original_solution() {
    let mut body = cfg(&[vec![1, 1, 2], vec![2, 3], vec![1, 3], vec![]], &[0, 2, 1, 0]);
    body.basic_blocks_mut()[BasicBlock::from_u32(2)].is_cleanup = true;
    let no_return = BTreeSet::new();
    let reachable = mir_reachable(&body, &no_return);
    assert_same(&body, &reachable, &no_return);
    assert_eq!(init_at_entry(&body, &reachable, &no_return)[2], None);
}

#[test]
fn an_explicitly_unreachable_entry_is_not_transferred() {
    let body = cfg(&[vec![1], vec![]], &[2, 0]);
    assert_same(&body, &[false, false], &BTreeSet::new());
    assert_eq!(init_at_entry(&body, &[false, false], &BTreeSet::new())[1], None);
}

#[test]
fn whole_local_drops_keep_live_then_dead_initialization() {
    let mut body = cfg(&[vec![1], vec![2], vec![4], vec![], vec![]], &[0; 5]);
    body.basic_blocks_mut()[BasicBlock::from_u32(3)].is_cleanup = true;
    for (block, target) in [(1, 2), (2, 4)] {
        body.basic_blocks_mut()[BasicBlock::from_u32(block)].terminator.as_mut().unwrap().kind =
            TerminatorKind::Drop {
                place: Local::from_u32(1).into(),
                target: BasicBlock::from_u32(target),
                unwind: mir::UnwindAction::Cleanup(BasicBlock::from_u32(3)),
                replace: false,
                drop: None,
            };
    }
    let no_return = BTreeSet::new();
    let reachable = mir_reachable(&body, &no_return);
    assert_same(&body, &reachable, &no_return);
    let entry = init_at_entry(&body, &reachable, &no_return);
    assert!(entry[1].as_ref().unwrap().maybe_init.contains(&Local::from_u32(1)));
    assert!(!entry[2].as_ref().unwrap().maybe_init.contains(&Local::from_u32(1)));
    assert_eq!(entry[3], None);
}

#[test]
fn call_destinations_and_dead_returns_keep_the_original_state() {
    let mut body = cfg(&[vec![1], vec![], vec![]], &[0; 3]);
    body.basic_blocks_mut()[BasicBlock::from_u32(2)].is_cleanup = true;
    body.basic_blocks_mut()[mir::START_BLOCK].terminator.as_mut().unwrap().kind =
        TerminatorKind::Call {
            func: Operand::Copy(Local::from_u32(1).into()),
            args: Box::new([]),
            destination: Local::from_u32(2).into(),
            target: Some(BasicBlock::from_u32(1)),
            unwind: mir::UnwindAction::Cleanup(BasicBlock::from_u32(2)),
            call_source: mir::CallSource::Normal,
            fn_span: DUMMY_SP,
        };
    for no_return in [BTreeSet::new(), BTreeSet::from([mir::START_BLOCK])] {
        let reachable = mir_reachable(&body, &no_return);
        assert_same(&body, &reachable, &no_return);
        let entry = init_at_entry(&body, &reachable, &no_return);
        if no_return.is_empty() {
            assert!(entry[1].as_ref().unwrap().maybe_init.contains(&Local::from_u32(2)));
        } else {
            assert_eq!(entry[1], None);
        }
        assert_eq!(entry[2], None);
    }
}

#[test]
fn yield_moves_and_resume_assignments_keep_the_original_state() {
    let mut body = cfg(&[vec![1], vec![], vec![]], &[0; 3]);
    body.basic_blocks_mut()[BasicBlock::from_u32(2)].is_cleanup = true;
    body.basic_blocks_mut()[mir::START_BLOCK].terminator.as_mut().unwrap().kind =
        TerminatorKind::Yield {
            value: Operand::Move(Local::from_u32(1).into()),
            resume: BasicBlock::from_u32(1),
            resume_arg: Local::from_u32(2).into(),
            drop: Some(BasicBlock::from_u32(2)),
        };
    let no_return = BTreeSet::new();
    let reachable = mir_reachable(&body, &no_return);
    assert_same(&body, &reachable, &no_return);
    let entry = init_at_entry(&body, &reachable, &no_return);
    assert_eq!(entry[1].as_ref().unwrap().maybe_init, BTreeSet::from([Local::from_u32(2)]));
    assert_eq!(entry[2], None);
}
