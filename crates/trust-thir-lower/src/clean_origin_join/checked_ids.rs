// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Check physical function IDs before the general Clean-origin join mutates
//! destination tables. This is structural admission, never proof authority.

use std::collections::BTreeSet;
use std::ops::ControlFlow;

use trust_ir::{Constant, FuncId, Inst, Module};

/// Check the complete physical function inventory before any join mutation.
/// Module IDs are keys, not vector positions: sparse inputs may be valid, but
/// the append-by-offset map must remain injective and disjoint from the owner.
pub(super) fn validate_join(destination: &Module, source: &Module) -> Result<(u32, u32), String> {
    let function_offset = u32::try_from(destination.functions.len())
        .map_err(|_| "destination function count exceeds u32")?;
    let global_offset = u32::try_from(destination.globals.len())
        .map_err(|_| "destination global count exceeds u32")?;
    let combined_globals = destination
        .globals
        .len()
        .checked_add(source.globals.len())
        .ok_or("combined global count overflows usize")?;
    u32::try_from(combined_globals).map_err(|_| "combined global count exceeds u32")?;
    let mut occupied = BTreeSet::new();
    for function in &destination.functions {
        if !occupied.insert(function.id.index()) {
            return Err("destination function IDs are ambiguous".to_owned());
        }
    }
    let mut source_ids = BTreeSet::new();
    for function in &source.functions {
        if source.func_types.get(function.ty.index() as usize).is_none() {
            return Err("source function signature is missing".to_owned());
        }
        if !source_ids.insert(function.id.index()) {
            return Err("source function IDs are ambiguous".to_owned());
        }
        let projected = function_offset
            .checked_add(function.id.index())
            .ok_or_else(|| "source function ID cannot be remapped without overflow".to_owned())?;
        if !occupied.insert(projected) {
            return Err(
                "appended function ID collides with an existing physical function".to_owned()
            );
        }
    }
    // Check the exact fields the later drain remaps. The public carrier is
    // unsealed, so a collector's earlier validation cannot replace this belt.
    for function in &source.functions {
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            match &node.inst {
                Inst::CallIndirect { sig, .. } => {
                    if source.func_types.get(sig.index() as usize).is_none() {
                        return Err("source indirect-call signature is missing".to_owned());
                    }
                }
                Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                    validate_function(*callee, &source_ids, function_offset)?;
                }
                Inst::SeqMap { fwd, .. } => {
                    validate_function(*fwd, &source_ids, function_offset)?;
                }
                Inst::Const { value, .. } => {
                    validate_constant(value, &source_ids, function_offset)?;
                }
                Inst::Switch { cases, .. } => {
                    for case in cases {
                        validate_constant(&case.value, &source_ids, function_offset)?;
                    }
                }
                Inst::GlobalAddr { global } => {
                    global_offset
                        .checked_add(global.index())
                        .ok_or("source global reference cannot be remapped without overflow")?;
                    if source.globals.get(global.index() as usize).is_none() {
                        return Err("source global reference is missing".to_owned());
                    }
                }
                _ => {}
            }
        }
    }
    for global in &source.globals {
        if let Some(value) = &global.initializer {
            validate_constant(value, &source_ids, function_offset)?;
        }
    }
    Ok((function_offset, global_offset))
}

fn validate_function(id: FuncId, source_ids: &BTreeSet<u32>, offset: u32) -> Result<(), String> {
    offset
        .checked_add(id.index())
        .ok_or("source function reference cannot be remapped without overflow")?;
    if !source_ids.contains(&id.index()) {
        return Err("source function reference is missing".to_owned());
    }
    Ok(())
}

fn validate_constant(
    value: &Constant,
    source_ids: &BTreeSet<u32>,
    offset: u32,
) -> Result<(), String> {
    // The IR's borrowed stack-safe walker visits every aggregate, record,
    // closure capture, and splat element once; it never expands a splat's len.
    match value.try_visit_constants(|constant| {
        let target = match constant {
            Constant::FnDef(target) | Constant::Closure { func: target, .. } => *target,
            _ => return ControlFlow::Continue(()),
        };
        match validate_function(target, source_ids, offset) {
            Ok(()) => ControlFlow::Continue(()),
            Err(reason) => ControlFlow::Break(reason),
        }
    }) {
        ControlFlow::Continue(()) => Ok(()),
        ControlFlow::Break(reason) => Err(reason),
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::{BlockId, FuncId, FuncTy, Function, Inst, ModuleFunctionCatalog, Ty};

    use super::*;

    pub(super) fn destination(ids: &[u32]) -> Module {
        let mut module = Module::new("physical-destination");
        let sig = module
            .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
            .expect("a fresh FuncTyId");
        for &id in ids {
            module.functions.push(Function::new(
                FuncId::new(id),
                format!("owner-{id}"),
                sig,
                BlockId::new(0),
            ));
        }
        module
    }

    #[test]
    fn duplicate_owner_and_source_ids_refuse_even_without_a_panic_site() {
        assert!(
            validate_join(&destination(&[5, 5]), &destination(&[0]))
                .unwrap_err()
                .contains("destination")
        );
        assert!(
            validate_join(&destination(&[5]), &destination(&[0, 0]))
                .unwrap_err()
                .contains("source")
        );
    }

    #[test]
    fn checked_offsets_cover_every_function_not_only_panic_entries() {
        assert!(
            validate_join(&destination(&[0]), &destination(&[u32::MAX]))
                .unwrap_err()
                .contains("overflow")
        );
        let (offset, _) = validate_join(&destination(&[]), &destination(&[u32::MAX])).unwrap();
        assert_eq!(offset, 0, "a zero offset preserves a unique representable sparse ID");
    }

    pub(super) fn general_pair() -> Module {
        let mut builder = trust_ir_build::ModuleBuilder::new("checked-general-pair");
        let sig = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut callee = builder.function("checked-callee", sig);
        let entry = callee.create_block();
        let value = callee.add_block_param(entry, Ty::U64);
        callee.switch_to_block(entry);
        callee.ret(vec![value]);
        callee.build();
        let mut caller = builder.function("checked-caller", sig);
        let entry = caller.create_block();
        let value = caller.add_block_param(entry, Ty::U64);
        caller.switch_to_block(entry);
        let returned = caller.call(FuncId::new(0), vec![value]);
        caller.ret(vec![returned]);
        caller.build();
        builder.build().expect("the checked general pair builds")
    }

    pub(super) fn append_general(
        dst: &mut Module,
        src: Module,
    ) -> super::super::CleanOriginJoinSummary {
        use super::super::{CleanOriginIrOutcome, GeneralCleanIr, GeneralOutcome, GeneralRow};
        let outcome = CleanOriginIrOutcome::General(GeneralCleanIr {
            rows: vec![GeneralRow {
                clean_name: "checked-pair".to_owned(),
                outcome: GeneralOutcome::Compiled { tv_mint_certified: false },
            }],
            module: Some(src),
        });
        let mut errors = Vec::new();
        let summary = super::super::append_clean_origin(dst, vec![outcome], &mut errors);
        assert!(errors.is_empty(), "{errors:?}");
        summary
    }

    #[test]
    fn public_append_collision_and_overflow_leave_all_data_tables_unpublished() {
        for (dst_ids, src_ids, reason) in [
            (vec![1], vec![0, 1], "collides"),
            (vec![5, 5], vec![0, 1], "destination"),
            (vec![0], vec![0, 0], "source"),
            (vec![0], vec![0, u32::MAX], "overflow"),
        ] {
            let mut dst = destination(&dst_ids);
            let before = dst.clone();
            let mut src = general_pair();
            for (function, id) in src.functions.iter_mut().zip(src_ids) {
                function.id = FuncId::new(id);
            }
            let summary = append_general(&mut dst, src);
            assert_eq!(summary.general.len(), 1, "the real compiled row must be disclosed");
            assert!(summary.general[0].3.contains(reason), "{:?}", summary.general);
            assert!(summary.general.iter().all(|(_, state, _, _)| *state == "merge-refused"));
            assert!(summary.general_functions.is_empty());
            assert_eq!(dst.functions, before.functions, "no colliding body is published");
            assert_eq!(dst.func_types, before.func_types, "validation precedes type interning");
            assert_eq!(dst.types, before.types);
            assert_eq!(dst.globals, before.globals);
        }
    }

    #[test]
    fn public_append_sparse_noncollision_preserves_the_internal_call_target() {
        let mut dst = destination(&[9]);
        let mut src = general_pair();
        src.functions[0].id = FuncId::new(3);
        src.functions[1].id = FuncId::new(7);
        for node in src.functions[1].blocks.iter_mut().flat_map(|block| &mut block.body) {
            if let Inst::Call { callee, .. } = &mut node.inst {
                *callee = FuncId::new(3);
            }
        }
        let summary = append_general(&mut dst, src);
        assert_eq!(summary.general.len(), 1, "the real compiled row must be disclosed");
        assert!(summary.general.iter().all(|(_, state, _, _)| *state == "compiled"));
        let catalog = ModuleFunctionCatalog::new(&dst);
        let callee = catalog.unique(FuncId::new(4)).unwrap();
        let caller = catalog.unique(FuncId::new(8)).unwrap();
        assert_eq!(callee.name, "checked-callee");
        assert!(caller.blocks.iter().flat_map(|block| &block.body).any(
            |node| matches!(node.inst, Inst::Call { callee, .. } if callee == FuncId::new(4))
        ));
        assert_eq!(catalog.unique(FuncId::new(9)).unwrap().name, "owner-9");
        assert!(catalog.ambiguous_ids().next().is_none());
    }
}

#[cfg(test)]
#[path = "checked_ids/reference_tests.rs"]
mod reference_tests;
