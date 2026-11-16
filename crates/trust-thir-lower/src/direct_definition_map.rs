// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Carry pass 1's exact local-definition assignments into publication.
//!
//! Names and display paths are not join keys. This is an association with the
//! assembled direct prefix, not a codegen license or a conservation verdict.
//! A malformed assignment leaves every definition unassociated.

use std::collections::BTreeMap;

use trust_ir::{FuncId, Module, Producer};

#[derive(Default)]
pub(crate) struct DirectDefinitionMap {
    by_def: BTreeMap<u32, FuncId>,
}

impl DirectDefinitionMap {
    pub(crate) fn from_assembly(module: &Module, assigned: &[(u32, FuncId)]) -> Self {
        let mut by_def: BTreeMap<u32, FuncId> = BTreeMap::new();
        for (position, &(def_index, id)) in assigned.iter().enumerate() {
            // Pass 1 assigns dense FuncIds in strictly increasing DefIndex order.
            // Do not turn a duplicate or a permuted assignment into first/last wins.
            if id.as_usize() != position
                || by_def.last_key_value().is_some_and(|(&previous, _)| previous >= def_index)
            {
                return Self::default();
            }
            let Some(function) = module.functions.get(position) else {
                return Self::default();
            };
            if function.id != id
                || function.is_declaration()
                || function.producer != Some(Producer::TRust)
            {
                return Self::default();
            }
            by_def.insert(def_index, id);
        }
        Self { by_def }
    }

    /// Length of the validated dense direct-source prefix; no license or verdict.
    pub(crate) fn len(&self) -> usize {
        self.by_def.len()
    }

    pub(crate) fn get(&self, def_index: u32) -> Option<FuncId> {
        self.by_def.get(&def_index).copied()
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::{Block, BlockId, FuncTyId, Function};

    use super::*;

    fn defined(id: u32, symbol: &str) -> Function {
        let mut function =
            Function::new(FuncId::new(id), symbol, FuncTyId::new(0), BlockId::new(0))
                .with_producer(Producer::TRust);
        function.display_path = Some("probe::{constant#0}::same".to_string());
        function.blocks.push(Block::new(BlockId::new(0)));
        function
    }

    fn module() -> Module {
        let mut module = Module::new("probe");
        module.functions = vec![
            defined(0, "_RNvCs1_5probe4same"),
            defined(1, "__trust_init_00000000000000000000000000000002"),
            defined(2, "_RNvCs3_5probe4same"),
        ];
        module
    }

    #[test]
    fn exact_definitions_survive_mangled_names_and_equal_display_paths() {
        let map = DirectDefinitionMap::from_assembly(
            &module(),
            &[(9, FuncId::new(0)), (71, FuncId::new(1)), (102, FuncId::new(2))],
        );
        for (definition, function) in [(9, 0), (71, 1), (102, 2)] {
            assert_eq!(map.get(definition), Some(FuncId::new(function)));
        }
        assert_eq!(map.get(0), None);
        assert_eq!(map.get(72), None);
    }

    #[test]
    fn malformed_assignments_never_keep_a_partial_or_ambiguous_join() {
        let assignments = [
            vec![(9, FuncId::new(0)), (9, FuncId::new(1))],
            vec![(71, FuncId::new(0)), (9, FuncId::new(1))],
            vec![(9, FuncId::new(1)), (71, FuncId::new(0))],
            vec![(9, FuncId::new(0)), (71, FuncId::new(0))],
            vec![(9, FuncId::new(0)), (71, FuncId::new(2))],
            vec![
                (9, FuncId::new(0)),
                (71, FuncId::new(1)),
                (102, FuncId::new(2)),
                (103, FuncId::new(3)),
            ],
        ];
        for assigned in assignments {
            let map = DirectDefinitionMap::from_assembly(&module(), &assigned);
            for definition in [9, 71, 102, 103] {
                assert_eq!(map.get(definition), None, "{assigned:?}");
            }
        }
    }

    #[test]
    fn a_missing_body_wrong_producer_or_renumbered_row_withdraws_the_join() {
        for changed in 0..4 {
            let mut module = module();
            match changed {
                0 => module.functions[1].blocks.clear(),
                1 => module.functions[1].producer = Some(Producer::Clean),
                2 => module.functions[1].producer = None,
                3 => module.functions[1].id = FuncId::new(7),
                _ => unreachable!(),
            }
            let map = DirectDefinitionMap::from_assembly(
                &module,
                &[(9, FuncId::new(0)), (71, FuncId::new(1))],
            );
            assert_eq!(map.get(9), None, "mutation {changed}");
            assert_eq!(map.get(71), None, "mutation {changed}");
        }
    }

    #[test]
    fn only_the_assigned_prefix_has_local_definition_associations() {
        let module = module();
        let empty = DirectDefinitionMap::from_assembly(&module, &[]);
        assert_eq!(empty.get(9), None);
        let prefix = DirectDefinitionMap::from_assembly(&module, &[(9, FuncId::new(0))]);
        assert_eq!(prefix.get(9), Some(FuncId::new(0)));
        assert_eq!(prefix.get(71), None);
    }
}
