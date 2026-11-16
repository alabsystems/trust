//! Which SSA values reach an actual instruction use, beyond branch transport.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};

use trust_ir::{Block, BlockId, Inst, InstrNode, ValueId};

/// Recover a field's exact SSA source through aggregate construction and
/// projection only. Loads, calls, control-flow joins and unknown producers do
/// not establish a source. A later write to the same field takes precedence.
pub(super) fn projected_value_source(
    blocks: &[Block],
    current: &[InstrNode],
    mut value: ValueId,
) -> Option<ValueId> {
    let mut fields = Vec::new();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(value) {
            return None;
        }
        let mut definitions = blocks
            .iter()
            .flat_map(|b| &b.body)
            .chain(current)
            .filter(|node| node.results.contains(&value));
        let definition = definitions.next();
        if definitions.next().is_some() {
            return None;
        }
        match definition.map(|node| &node.inst) {
            Some(Inst::ExtractField { aggregate, field, .. }) => {
                fields.push(*field);
                value = *aggregate;
            }
            Some(Inst::InsertField { aggregate, field, value: inserted, .. })
                if !fields.is_empty() =>
            {
                if fields.last() == Some(field) {
                    fields.pop();
                    value = *inserted;
                } else {
                    value = *aggregate;
                }
            }
            _ => return fields.is_empty().then_some(value),
        }
    }
}

/// A branch argument only transports a value to a block parameter. Other
/// operand occurrences are uses, including a condition which is also passed
/// as a branch argument. Walk transport edges backwards from those uses.
/// The canonical operand visitor currently visits each occurrence, including
/// repeated ValueIds; the single-edge switch test locks down that dependency.
/// This is a use analysis, not IR validation: type, dominance and instruction
/// placement checks remain the responsibility of the normal module validator.
pub(super) fn used_values(blocks: &[Block], proof_values: &[ValueId]) -> HashSet<ValueId> {
    let targets: HashMap<BlockId, &Block> = blocks.iter().map(|b| (b.id, b)).collect();
    let mut parents: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    let mut used: HashSet<_> = proof_values.iter().copied().collect();
    let mut malformed = targets.len() != blocks.len();
    for block in blocks {
        for node in &block.body {
            let mut transported: HashMap<ValueId, usize> = HashMap::new();
            for edge in node.inst.successor_edges() {
                let Some(target) = targets.get(&edge.target) else {
                    malformed = true;
                    continue;
                };
                if edge.args.len() != target.params.len() {
                    malformed = true;
                    continue;
                }
                for (arg, (param, _)) in edge.args.iter().zip(&target.params) {
                    parents.entry(*param).or_default().push(*arg);
                    *transported.entry(*arg).or_default() += 1;
                }
            }
            // Subtract occurrences, not membership: a condition/callee may
            // also be an edge argument, and that independent use must survive.
            node.inst.visit_value_operands(|value| {
                if node.proofs.is_empty() && node.proof_context.is_none() {
                    if let Some(count) = transported.get_mut(&value) {
                        if *count > 0 {
                            *count -= 1;
                            return;
                        }
                    }
                }
                used.insert(value);
            });
            if node.proofs.is_empty() && node.proof_context.is_none() {
                malformed |= transported.values().any(|count| *count != 0);
            }
        }
    }
    if malformed {
        // Missing targets, mismatched arities, duplicate block IDs or a changed
        // operand-visitor contract make transport classification uncertain.
        // Keep all operands live in those cases; this is not a full CFG check.
        for block in blocks {
            for node in &block.body {
                node.inst.visit_value_operands(|value| {
                    used.insert(value);
                });
                for edge in node.inst.successor_edges() {
                    used.extend(edge.args.iter().copied());
                }
            }
        }
    }
    let mut pending: Vec<_> = used.iter().copied().collect();
    while let Some(value) = pending.pop() {
        if let Some(incoming) = parents.get(&value) {
            for predecessor in incoming {
                if used.insert(*predecessor) {
                    pending.push(*predecessor);
                }
            }
        }
    }
    used
}

#[cfg(test)]
mod tests {
    use trust_ir::{Inst, InstrNode, Ty};

    use super::*;

    fn insert(result: u32, aggregate: u32, field: u32, value: u32) -> InstrNode {
        InstrNode::new(Inst::InsertField {
            ty: Ty::Tuple(vec![Ty::Ptr, Ty::Ptr]),
            aggregate: ValueId::new(aggregate),
            field,
            value: ValueId::new(value),
        })
        .with_result(ValueId::new(result))
    }

    fn extract(result: u32, aggregate: u32, field: u32) -> InstrNode {
        InstrNode::new(Inst::ExtractField {
            ty: Ty::Ptr,
            aggregate: ValueId::new(aggregate),
            field,
        })
        .with_result(ValueId::new(result))
    }

    #[test]
    fn projected_source_follows_exact_field_and_last_write() {
        let nodes = [
            insert(10, 1, 0, 2),
            insert(11, 10, 1, 3),
            insert(12, 11, 0, 4),
            extract(13, 12, 0),
            extract(14, 12, 1),
        ];
        assert_eq!(projected_value_source(&[], &nodes, ValueId::new(13)), Some(ValueId::new(4)));
        assert_eq!(projected_value_source(&[], &nodes, ValueId::new(14)), Some(ValueId::new(3)));
    }

    #[test]
    fn projected_source_follows_nested_aggregates_across_blocks() {
        let mut block = Block::new(BlockId::new(0));
        block.body = vec![insert(10, 1, 0, 2), insert(11, 1, 1, 10)];
        let current = [extract(12, 11, 1), extract(13, 12, 0)];
        assert_eq!(
            projected_value_source(&[block], &current, ValueId::new(13)),
            Some(ValueId::new(2))
        );
    }

    #[test]
    fn projected_source_does_not_invent_unknown_field_provenance() {
        let nodes = [extract(10, 1, 0)];
        assert_eq!(projected_value_source(&[], &nodes, ValueId::new(10)), None);
    }

    #[test]
    fn projected_source_refuses_duplicate_definitions_and_cycles() {
        let duplicates = [insert(10, 1, 0, 2), insert(10, 1, 0, 3), extract(11, 10, 0)];
        assert_eq!(projected_value_source(&[], &duplicates, ValueId::new(11)), None);
        let cyclic = [insert(10, 10, 1, 2), extract(11, 10, 0)];
        assert_eq!(projected_value_source(&[], &cyclic, ValueId::new(11)), None);
    }

    fn block(id: u32, params: &[u32], inst: Inst) -> Block {
        let mut block = Block::new(BlockId::new(id));
        block.params = params.iter().map(|v| (ValueId::new(*v), Ty::Bool)).collect();
        block.body.push(InstrNode::new(inst));
        block
    }

    #[test]
    fn dead_transport_chain_is_not_a_use() {
        let blocks = [
            block(0, &[1], Inst::Br { target: BlockId::new(1), args: vec![ValueId::new(1)] }),
            block(1, &[2], Inst::Br { target: BlockId::new(2), args: vec![ValueId::new(2)] }),
            block(2, &[3], Inst::Return { values: vec![] }),
        ];
        assert!(used_values(&blocks, &[]).is_empty());
    }

    #[test]
    fn returned_transport_chain_keeps_every_predecessor_live() {
        let blocks = [
            block(0, &[1], Inst::Br { target: BlockId::new(1), args: vec![ValueId::new(1)] }),
            block(1, &[2], Inst::Br { target: BlockId::new(2), args: vec![ValueId::new(2)] }),
            block(2, &[3], Inst::Return { values: vec![ValueId::new(3)] }),
        ];
        assert_eq!(used_values(&blocks, &[]), [1, 2, 3].map(ValueId::new).into_iter().collect());
    }

    #[test]
    fn condition_also_passed_as_dead_argument_still_counts_as_a_use() {
        let blocks = [
            block(
                0,
                &[1],
                Inst::CondBr {
                    cond: ValueId::new(1),
                    then_target: BlockId::new(1),
                    then_args: vec![ValueId::new(1)],
                    else_target: BlockId::new(2),
                    else_args: vec![ValueId::new(1)],
                },
            ),
            block(1, &[2], Inst::Return { values: vec![] }),
            block(2, &[3], Inst::Return { values: vec![] }),
        ];
        assert!(used_values(&blocks, &[]).contains(&ValueId::new(1)));
    }

    #[test]
    fn single_edge_switch_preserves_discriminant_occurrence() {
        let mut blocks = [
            block(
                0,
                &[1],
                Inst::Switch {
                    value: ValueId::new(1),
                    default: BlockId::new(1),
                    default_args: vec![ValueId::new(1)],
                    cases: vec![],
                    exhaustive_enum_unreachable: false,
                },
            ),
            block(1, &[2], Inst::Return { values: vec![] }),
        ];
        blocks[0].params[0].1 = Ty::U32;
        blocks[1].params[0].1 = Ty::U32;
        // With only one transport occurrence, a visitor that deduplicates
        // ValueIds would silently swallow the independent discriminant use.
        assert_eq!(used_values(&blocks, &[]), [ValueId::new(1)].into_iter().collect());
    }

    #[test]
    fn malformed_transport_does_not_erase_its_argument_use() {
        let blocks =
            [block(0, &[1], Inst::Br { target: BlockId::new(1), args: vec![ValueId::new(1)] })];
        assert!(used_values(&blocks, &[]).contains(&ValueId::new(1)));
    }

    #[test]
    fn cyclic_transport_reaches_a_fixed_point_for_dead_and_returned_values() {
        let mut blocks = [
            block(0, &[1, 9], Inst::Br { target: BlockId::new(1), args: vec![ValueId::new(1)] }),
            block(
                1,
                &[2],
                Inst::CondBr {
                    cond: ValueId::new(9),
                    then_target: BlockId::new(1),
                    then_args: vec![ValueId::new(2)],
                    else_target: BlockId::new(2),
                    else_args: vec![ValueId::new(2)],
                },
            ),
            block(2, &[3], Inst::Return { values: vec![] }),
        ];
        assert_eq!(used_values(&blocks, &[]), [ValueId::new(9)].into_iter().collect());
        blocks[2].body[0] = InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] });
        assert_eq!(used_values(&blocks, &[]), [1, 2, 3, 9].map(ValueId::new).into_iter().collect());
    }

    #[test]
    fn a_proof_binding_keeps_transported_values_live() {
        let blocks = [
            block(0, &[1], Inst::Br { target: BlockId::new(1), args: vec![ValueId::new(1)] }),
            block(1, &[2], Inst::Return { values: vec![] }),
        ];
        assert_eq!(
            used_values(&blocks, &[ValueId::new(2)]),
            [1, 2].map(ValueId::new).into_iter().collect()
        );
    }
}
