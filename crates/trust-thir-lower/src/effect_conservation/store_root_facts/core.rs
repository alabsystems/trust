//! Reaching copies of entry arguments, independent of MIR's coarse root census.
//!
//! An exact fact describes the value of a local, not a no-alias property of its
//! pointee. The adapter supplies every possible control-flow edge and invalidates
//! unknown definitions. Locals whose storage can be modified through an alias
//! must be marked exposed for the whole analysis.

use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub(super) enum Step {
    /// Copy the source's pre-step fact, consume moves, then define the destination.
    /// `None` denotes a definition that is not an exact local-to-local copy.
    Assign {
        dst: usize,
        src: Option<usize>,
        moved: Vec<usize>,
    },
    Kill(Vec<usize>),
    KillAll,
    Observe,
}

#[derive(Clone, Debug)]
pub(super) struct Block {
    pub steps: Vec<Step>,
    pub successors: Vec<usize>,
}

#[derive(Clone, Debug)]
pub(super) struct Program {
    pub locals: usize,
    /// Entry argument local indices, in argument order (not arbitrary origins).
    pub arguments: Vec<usize>,
    pub exposed: Vec<bool>,
    pub blocks: Vec<Block>,
}

type State = Vec<Option<u32>>;
type Snapshot = Vec<(usize, u32)>;

#[derive(Debug)]
pub(super) struct Facts {
    // None is unreachable, distinct from a reachable state with no exact facts.
    // Snapshots are sparse, sorted by local, and recorded before existing steps.
    before: Vec<Option<Vec<Snapshot>>>,
}

impl Facts {
    pub(super) fn at(&self, block: usize, step: usize, local: usize) -> Option<u32> {
        let snapshot = self.before.get(block)?.as_ref()?.get(step)?;
        let index = snapshot
            .binary_search_by_key(&local, |&(local, _)| local)
            .ok()?;
        Some(snapshot[index].1)
    }
}

fn valid(program: &Program) -> bool {
    if program.exposed.len() != program.locals {
        return false;
    }
    if program
        .arguments
        .iter()
        .enumerate()
        .any(|(index, &local)| local >= program.locals || u32::try_from(index).is_err())
    {
        return false;
    }
    let mut argument_local = vec![false; program.locals];
    for &local in &program.arguments {
        if argument_local[local] {
            return false;
        }
        argument_local[local] = true;
    }
    let in_bounds = |&local: &usize| local < program.locals;
    program.blocks.iter().all(|block| {
        block
            .successors
            .iter()
            .all(|&block| block < program.blocks.len())
            && block.steps.iter().all(|step| match step {
                Step::Assign { dst, src, moved } => {
                    *dst < program.locals
                        && src.is_none_or(|src| src < program.locals)
                        && moved.iter().all(in_bounds)
                }
                Step::Kill(locals) => locals.iter().all(in_bounds),
                Step::KillAll | Step::Observe => true,
            })
    })
}

fn transfer(state: &mut [Option<u32>], step: &Step, exposed: &[bool]) {
    match step {
        Step::Assign { dst, src, moved } => {
            // A move invalidates its source after the RHS was evaluated. This
            // also handles a self move without discarding the copied value.
            let source = src.and_then(|src| state[src]);
            for &local in moved {
                state[local] = None;
            }
            state[*dst] = if exposed[*dst] { None } else { source };
        }
        Step::Kill(locals) => {
            for &local in locals {
                state[local] = None;
            }
        }
        Step::KillAll => state.fill(None),
        Step::Observe => {}
    }
}

/// Compute exact reaching entry-argument copies. Malformed programs fail closed:
/// no query returns an exact fact. Block zero has an implicit entry predecessor;
/// other blocks become reachable only through the supplied successors.
pub(super) fn analyze(program: &Program) -> Facts {
    if !valid(program) || program.blocks.is_empty() {
        return Facts { before: Vec::new() };
    }

    let mut entry = vec![None; program.locals];
    for (argument, &local) in program.arguments.iter().enumerate() {
        if !program.exposed[local] {
            entry[local] = Some(argument as u32);
        }
    }

    let mut incoming: Vec<Option<State>> = vec![None; program.blocks.len()];
    incoming[0] = Some(entry);
    let mut pending = VecDeque::from([0]);
    let mut queued = vec![false; program.blocks.len()];
    queued[0] = true;
    let mut state = vec![None; program.locals];

    while let Some(block) = pending.pop_front() {
        queued[block] = false;
        state.copy_from_slice(incoming[block].as_ref().expect("queued block is reachable"));
        for step in &program.blocks[block].steps {
            transfer(&mut state, step, &program.exposed);
        }
        for &successor in &program.blocks[block].successors {
            let changed = match &mut incoming[successor] {
                None => {
                    // Bottom becomes reachable even when all facts are unknown.
                    incoming[successor] = Some(state.clone());
                    true
                }
                Some(prior) => {
                    let mut changed = false;
                    for (prior, &next) in prior.iter_mut().zip(&state) {
                        if prior.is_some() && *prior != next {
                            *prior = None;
                            changed = true;
                        }
                    }
                    changed
                }
            };
            if changed && !queued[successor] {
                queued[successor] = true;
                pending.push_back(successor);
            }
        }
    }

    // Fixed-point iteration stores one state per block and reuses its scratch
    // state. Materialize per-location facts only once, after convergence.
    let before = program
        .blocks
        .iter()
        .zip(incoming)
        .map(|(block, incoming)| {
            let mut state = incoming?;
            Some(
                block
                    .steps
                    .iter()
                    .map(|step| {
                        let snapshot = state
                            .iter()
                            .enumerate()
                            .filter_map(|(local, &argument)| argument.map(|arg| (local, arg)))
                            .collect();
                        transfer(&mut state, step, &program.exposed);
                        snapshot
                    })
                    .collect(),
            )
        })
        .collect();
    Facts { before }
}

#[cfg(test)]
mod tests {
    use super::{Block, Facts, Program, Step, analyze};

    fn block(steps: Vec<Step>, successors: &[usize]) -> Block {
        Block {
            steps,
            successors: successors.to_vec(),
        }
    }

    fn program(blocks: Vec<Block>) -> Program {
        Program {
            locals: 4,
            arguments: vec![0, 1],
            exposed: vec![false; 4],
            blocks,
        }
    }

    fn copy(dst: usize, src: usize) -> Step {
        Step::Assign {
            dst,
            src: Some(src),
            moved: vec![],
        }
    }

    fn assert_no_facts(facts: &Facts) {
        for block in 0..5 {
            for step in 0..5 {
                for local in 0..5 {
                    assert_eq!(facts.at(block, step, local), None);
                }
            }
        }
    }

    #[test]
    fn before_and_after_argument_reassignment_are_distinct() {
        let facts = analyze(&program(vec![block(
            vec![
                Step::Observe,
                copy(0, 1),
                Step::Observe,
                copy(2, 0),
                Step::Observe,
            ],
            &[],
        )]));
        assert_eq!(facts.at(0, 0, 0), Some(0));
        assert_eq!(facts.at(0, 1, 0), Some(0));
        assert_eq!(facts.at(0, 2, 0), Some(1));
        assert_eq!(facts.at(0, 3, 2), None);
        assert_eq!(facts.at(0, 4, 2), Some(1));
    }

    #[test]
    fn unknown_definition_kills_and_later_copy_recovers() {
        let facts = analyze(&program(vec![block(
            vec![
                copy(2, 0),
                Step::Observe,
                Step::Assign {
                    dst: 2,
                    src: None,
                    moved: vec![],
                },
                Step::Observe,
                copy(2, 1),
                Step::Observe,
            ],
            &[],
        )]));
        assert_eq!(facts.at(0, 1, 2), Some(0));
        assert_eq!(facts.at(0, 3, 2), None);
        assert_eq!(facts.at(0, 5, 2), Some(1));
    }

    #[test]
    fn move_uses_prestate_and_consumes_all_moved_sources() {
        let facts = analyze(&program(vec![block(
            vec![
                Step::Assign {
                    dst: 2,
                    src: Some(0),
                    moved: vec![0, 1],
                },
                Step::Observe,
            ],
            &[],
        )]));
        assert_eq!(facts.at(0, 0, 0), Some(0));
        assert_eq!(facts.at(0, 1, 0), None);
        assert_eq!(facts.at(0, 1, 1), None);
        assert_eq!(facts.at(0, 1, 2), Some(0));
    }

    #[test]
    fn self_move_defines_the_prestate_value() {
        let facts = analyze(&program(vec![block(
            vec![
                Step::Assign {
                    dst: 0,
                    src: Some(0),
                    moved: vec![0],
                },
                Step::Observe,
            ],
            &[],
        )]));
        assert_eq!(facts.at(0, 1, 0), Some(0));
    }

    #[test]
    fn storage_kills_and_opaque_kill_all_do_not_preserve_origins() {
        let facts = analyze(&program(vec![block(
            vec![
                copy(2, 0),
                Step::Kill(vec![0, 2]),
                Step::Observe,
                copy(2, 1),
                Step::Observe,
                Step::KillAll,
                Step::Observe,
                copy(2, 1),
                Step::Observe,
            ],
            &[],
        )]));
        assert_eq!(facts.at(0, 2, 0), None);
        assert_eq!(facts.at(0, 2, 1), Some(1));
        assert_eq!(facts.at(0, 2, 2), None);
        assert_eq!(facts.at(0, 4, 2), Some(1));
        for local in 0..4 {
            assert_eq!(facts.at(0, 6, local), None);
            assert_eq!(facts.at(0, 8, local), None);
        }
    }

    #[test]
    fn globally_exposed_storage_never_receives_an_exact_fact() {
        let mut input = program(vec![block(
            vec![
                Step::Observe,
                copy(0, 1),
                copy(2, 0),
                copy(3, 1),
                Step::Observe,
            ],
            &[],
        )]);
        input.exposed[0] = true;
        input.exposed[3] = true;
        let facts = analyze(&input);
        assert_eq!(facts.at(0, 0, 0), None);
        assert_eq!(facts.at(0, 4, 0), None);
        assert_eq!(facts.at(0, 4, 2), None);
        assert_eq!(facts.at(0, 4, 3), None);
        assert_eq!(facts.at(0, 4, 1), Some(1));
    }

    #[test]
    fn agreeing_diamond_preserves_the_exact_argument() {
        let facts = analyze(&program(vec![
            block(vec![], &[1, 2]),
            block(vec![copy(2, 1)], &[3]),
            block(vec![copy(2, 1)], &[3]),
            block(vec![Step::Observe], &[]),
        ]));
        assert_eq!(facts.at(3, 0, 2), Some(1));
    }

    #[test]
    fn conflicting_or_unknown_join_loses_the_fact() {
        for second in [
            copy(2, 1),
            Step::Assign {
                dst: 2,
                src: None,
                moved: vec![],
            },
        ] {
            let facts = analyze(&program(vec![
                block(vec![], &[1, 2]),
                block(vec![copy(2, 0)], &[3]),
                block(vec![second], &[3]),
                block(vec![Step::Observe], &[]),
            ]));
            assert_eq!(facts.at(3, 0, 2), None);
            assert_eq!(facts.at(3, 0, 1), Some(1));
        }
    }

    #[test]
    fn unreachable_predecessor_does_not_contaminate_reachable_join() {
        let facts = analyze(&program(vec![
            block(vec![copy(2, 0)], &[2]),
            block(vec![copy(2, 1), Step::Observe], &[2]),
            block(vec![Step::Observe], &[]),
        ]));
        assert_eq!(facts.at(1, 1, 2), None);
        assert_eq!(facts.at(2, 0, 2), Some(0));
    }

    #[test]
    fn reachable_unknown_predecessor_is_not_treated_as_unreachable() {
        let facts = analyze(&program(vec![
            block(vec![], &[1, 2]),
            block(vec![copy(2, 0)], &[3]),
            block(vec![], &[3]),
            block(vec![Step::Observe], &[]),
        ]));
        assert_eq!(facts.at(3, 0, 2), None);
    }

    #[test]
    fn loop_loses_conflicting_entry_fact_but_strong_update_recovers() {
        let facts = analyze(&program(vec![
            block(vec![], &[1]),
            block(vec![Step::Observe, copy(0, 1), Step::Observe], &[1, 2]),
            block(vec![Step::Observe], &[]),
        ]));
        assert_eq!(facts.at(1, 0, 0), None);
        assert_eq!(facts.at(1, 2, 0), Some(1));
        assert_eq!(facts.at(2, 0, 0), Some(1));
    }

    #[test]
    fn backedge_to_start_keeps_implicit_entry_predecessor() {
        let facts = analyze(&program(vec![block(
            vec![Step::Observe, copy(0, 1), Step::Observe],
            &[0],
        )]));
        assert_eq!(facts.at(0, 0, 0), None);
        assert_eq!(facts.at(0, 2, 0), Some(1));
    }

    #[test]
    fn duplicate_edges_and_late_predecessor_update_reach_fixed_point() {
        let facts = analyze(&program(vec![
            block(vec![copy(2, 0)], &[1, 2, 1]),
            block(vec![Step::Observe], &[3]),
            block(vec![copy(2, 1)], &[1]),
            block(vec![Step::Observe], &[]),
        ]));
        assert_eq!(facts.at(1, 0, 2), None);
        assert_eq!(facts.at(3, 0, 2), None);
        assert_eq!(facts.at(3, 0, 1), Some(1));
    }

    #[test]
    fn invalid_programs_return_no_partial_exact_facts() {
        let base = program(vec![block(vec![Step::Observe], &[])]);
        let mut invalid = Vec::new();
        let mut input = base.clone();
        input.exposed.pop();
        invalid.push(input);
        let mut input = base.clone();
        input.arguments = vec![0, 0];
        invalid.push(input);
        let mut input = base.clone();
        input.arguments.push(4);
        invalid.push(input);
        let mut input = base.clone();
        input.blocks[0].successors.push(1);
        invalid.push(input);
        for step in [
            copy(4, 0),
            copy(0, 4),
            Step::Assign {
                dst: 2,
                src: Some(0),
                moved: vec![4],
            },
            Step::Kill(vec![4]),
        ] {
            let mut input = base.clone();
            // The preceding observation must not leak entry facts when a later
            // malformed step makes the whole input invalid.
            input.blocks[0].steps.push(step);
            invalid.push(input);
        }
        for input in invalid {
            assert_no_facts(&analyze(&input));
        }
    }

    #[test]
    fn empty_program_and_out_of_bounds_queries_are_unknown() {
        assert_no_facts(&analyze(&program(vec![])));
        let facts = analyze(&program(vec![block(vec![Step::Observe], &[])]));
        assert_eq!(facts.at(0, 0, 0), Some(0));
        assert_eq!(facts.at(0, 1, 0), None);
        assert_eq!(facts.at(1, 0, 0), None);
        assert_eq!(facts.at(0, 0, 4), None);
        assert_eq!(facts.at(usize::MAX, usize::MAX, usize::MAX), None);
    }
}
