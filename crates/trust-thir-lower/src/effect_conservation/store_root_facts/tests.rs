use rustc_index::IndexVec;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, BasicBlockData, SourceInfo, Statement, Terminator, WithRetag};
use rustc_span::DUMMY_SP;

use super::*;

fn copy(dst: u32, src: u32) -> StatementKind<'static> {
    StatementKind::Assign(Box::new((
        Local::from_u32(dst).into(),
        Rvalue::Use(Operand::Copy(Local::from_u32(src).into()), WithRetag::No),
    )))
}
fn cfg(
    statements: Vec<Vec<StatementKind<'static>>>,
    edges: Vec<Vec<usize>>,
) -> (Body<'static>, StoreRootFacts) {
    let info = SourceInfo::outermost(DUMMY_SP);
    let blocks = statements.into_iter().map(|statements| {
        let mut block = BasicBlockData::new(
            Some(Terminator { source_info: info, kind: TerminatorKind::Return }),
            false,
        );
        block.statements = statements.into_iter().map(|kind| Statement::new(info, kind)).collect();
        block
    });
    let mut body = Body::new_cfg_only(IndexVec::from_iter(blocks));
    body.arg_count = 2;
    let reachable = vec![true; body.basic_blocks.len()];
    let facts = StoreRootFacts::for_cfg(&body, 5, &reachable, edges);
    (body, facts)
}
fn at(facts: &StoreRootFacts, block: usize, statement_index: usize, local: u32) -> Option<u32> {
    facts.argument_at(
        Location { block: BasicBlock::from_usize(block), statement_index },
        Local::from_u32(local),
    )
}

#[test]
fn actual_mir_strong_update_is_observed_before_and_after_reassignment() {
    let (_, facts) = cfg(vec![vec![copy(1, 2), StatementKind::Nop]], vec![vec![]]);
    assert_eq!(at(&facts, 0, 0, 1), Some(0));
    assert_eq!(at(&facts, 0, 1, 1), Some(1));
    assert_eq!(at(&facts, 0, 2, 1), Some(1));
}

#[test]
fn actual_mir_conflicting_joins_and_loop_backedges_are_unknown() {
    let (_, facts) = cfg(vec![vec![], vec![copy(1, 2)], vec![]], vec![vec![1, 2], vec![2], vec![]]);
    assert_eq!(at(&facts, 2, 0, 1), None);
    let (_, facts) = cfg(vec![vec![], vec![copy(1, 2)], vec![]], vec![vec![1], vec![1, 2], vec![]]);
    assert_eq!(at(&facts, 1, 0, 1), None);
    assert_eq!(at(&facts, 2, 0, 1), Some(1));
}

#[test]
fn actual_mir_storage_and_unknown_definitions_kill_but_copy_recovers() {
    let (_, facts) = cfg(
        vec![vec![StatementKind::StorageDead(Local::from_u32(1)), copy(1, 2), copy(1, 4)]],
        vec![vec![]],
    );
    assert_eq!(at(&facts, 0, 1, 1), None);
    assert_eq!(at(&facts, 0, 2, 1), Some(1));
    assert_eq!(at(&facts, 0, 3, 1), None);
}

#[test]
fn actual_mir_moves_preserve_copy_value_and_kill_source() {
    let moved = StatementKind::Assign(Box::new((
        Local::from_u32(3).into(),
        Rvalue::Use(Operand::Move(Local::from_u32(1).into()), WithRetag::No),
    )));
    let (_, facts) = cfg(vec![vec![moved]], vec![vec![]]);
    assert_eq!(at(&facts, 0, 1, 1), None);
    assert_eq!(at(&facts, 0, 1, 3), Some(0));
}

#[test]
fn actual_mir_call_destination_is_unknown_and_argument_move_precedes_store() {
    let (mut body, _) = cfg(vec![vec![], vec![]], vec![vec![1], vec![]]);
    body.basic_blocks_mut()[mir::START_BLOCK].terminator.as_mut().unwrap().kind =
        TerminatorKind::Call {
            func: Operand::Copy(Local::from_u32(4).into()),
            args: vec![rustc_span::Spanned {
                node: Operand::Move(Local::from_u32(1).into()),
                span: DUMMY_SP,
            }]
            .into_boxed_slice(),
            destination: Local::from_u32(2).into(),
            target: Some(BasicBlock::from_u32(1)),
            unwind: mir::UnwindAction::Unreachable,
            call_source: mir::CallSource::Normal,
            fn_span: DUMMY_SP,
        };
    let facts = StoreRootFacts::for_cfg(&body, 5, &[true, true], vec![vec![1], vec![]]);
    assert_eq!(at(&facts, 0, 0, 1), None);
    assert_eq!(at(&facts, 0, 0, 2), Some(1));
    assert_eq!(at(&facts, 1, 0, 2), None);
}

#[test]
fn actual_mir_address_exposure_bans_the_local_on_every_path() {
    let address = StatementKind::Assign(Box::new((
        Local::from_u32(3).into(),
        Rvalue::RawPtr(mir::RawPtrKind::Mut, Local::from_u32(1).into()),
    )));
    let (_, facts) = cfg(vec![vec![address, copy(1, 2)]], vec![vec![]]);
    assert_eq!(at(&facts, 0, 0, 1), None);
    assert_eq!(at(&facts, 0, 2, 1), None);
    assert_eq!(at(&facts, 0, 2, 2), Some(1));
}

#[test]
fn unreachable_exposure_and_definitions_do_not_pollute_reachable_paths() {
    let address = StatementKind::Assign(Box::new((
        Local::from_u32(3).into(),
        Rvalue::RawPtr(mir::RawPtrKind::Mut, Local::from_u32(1).into()),
    )));
    let (body, _) = cfg(vec![vec![], vec![address]], vec![vec![], vec![]]);
    let facts = StoreRootFacts::for_cfg(&body, 5, &[true, false], vec![vec![], vec![]]);
    assert_eq!(at(&facts, 0, 0, 1), Some(0));
    assert_eq!(at(&facts, 1, 0, 1), None);
}
