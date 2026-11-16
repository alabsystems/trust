// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Fetched proof construction, reused from the canonical TrustIR atomic replay.
//! Every lookup reflects the caller's original module; no module is authored here.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 4_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn truth(assembler: &mut Assembler<'_>, guard: Expr) -> PendingEquality {
    assembler.conversion(c("Bool"), guard, c("Bool.true")).unwrap()
}
fn atomic_evaluation(context: Expr) -> Expr {
    let u64_ty = app("IRTy.uint_", [nat(64)]);
    let layout =
        app("IRByteLayoutV1.mk", [u64_ty, nat(8), nat(8), list("IRTy", &[]), list("Nat", &[])]);
    app(
        "ir_byte_fetch_add_relaxed_u64_seq_below_v1",
        [
            context,
            memory(77),
            nat(16),
            nat(41),
            nat(7),
            app("Nat.le_add_right", [nat(17), nat(u64::MAX - 16)]),
            refl(
                app("IROption", [c("IRByteLayoutV1")]),
                app("IROption.some", [c("IRByteLayoutV1"), layout]),
            ),
            refl(c("Bool"), c("Bool.true")),
            app("ir_byte_u64_rep_write_v1", [memory_from(background(77)), nat(16), nat(41)]),
            app("Nat.le_add_right", [nat(49), nat(u64::MAX - 48)]),
        ],
    )
}

pub(super) fn assemble(module: &Module) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FuncId::new(0), 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FuncId::new(0)).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[pointer(16)]);
    let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory(77)));
    let entry_guard = truth(&mut assembler, entry.admission(&model, arguments.clone()).unwrap());
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            arguments,
            memory(77),
            nat(37),
            memory_guard,
            entry_guard,
        )
        .unwrap();
    let mut current = initialized.current().clone();
    let mut valid = initialized.valid().clone();
    let mut prefix = assembler.zero(&model, current.running(&model)).unwrap();
    for pc in 0..6 {
        let site = catalog
            .fetch(Coordinate { function: FuncId::new(0), block: BlockId::new(0), instruction: pc })
            .unwrap();
        let transfer = if pc == 1 || pc == 5 {
            let result = MemoryResult {
                value: if pc == 1 { pointer(16) } else { scalar(41) },
                memory: if pc == 1 { memory(77) } else { written(77, 48) },
            };
            let checks = site.memory_checks(&model, &current, &result).unwrap();
            let evaluated = if pc == 5 {
                // The primitive theorem derives the result from bytes/layout/
                // access/bounds. The enclosing kernel replay checks that this
                // very evaluator uses the fetched operands and current memory.
                PendingEquality::candidate(
                    c("IRByteMemoryResultV1"),
                    checks.evaluation,
                    result.result(),
                    atomic_evaluation(model.context().clone()),
                )
            } else {
                assembler
                    .conversion(c("IRByteMemoryResultV1"), checks.evaluation, result.result())
                    .unwrap()
            };
            let guard = truth(&mut assembler, checks.result);
            let allocations = assembler
                .conversion(
                    app("IRList", [c("IRByteAllocationV1")]),
                    app("ir_byte_mem_allocs_v1", [result.memory.clone()]),
                    app(
                        "ir_byte_mem_allocs_v1",
                        [app("ir_byte_world_memory_v1", [c("Nat"), current.world.clone()])],
                    ),
                )
                .unwrap();
            let transferred = site
                .memory_value(
                    &mut assembler,
                    &model,
                    &current,
                    result,
                    MemoryPremises { evaluated, result: guard, allocations, before: valid.clone() },
                )
                .unwrap();
            (transferred.current().clone(), transferred.valid().clone(), transferred.run().clone())
        } else {
            let value = match pc {
                0 => scalar(0),
                2 | 3 => pointer(16),
                4 => scalar(7),
                _ => unreachable!(),
            };
            let checks = site.scalar_checks(&model, &current, value.clone()).unwrap();
            let evaluated = assembler
                .conversion(
                    c("IRStepResult"),
                    checks.evaluation,
                    app("IRStepResult.value", [value.clone()]),
                )
                .unwrap();
            let operands = truth(&mut assembler, checks.operands);
            let result = truth(&mut assembler, checks.result);
            let transferred = site
                .scalar_value(
                    &mut assembler,
                    &model,
                    &current,
                    value,
                    ScalarPremises { evaluated, operands, result, before: valid.clone() },
                )
                .unwrap();
            (transferred.current().clone(), transferred.valid().clone(), transferred.run().clone())
        };
        (current, valid) = (transfer.0, transfer.1);
        prefix = assembler.concatenate(prefix, transfer.2).unwrap();
    }
    let branching = catalog
        .fetch(Coordinate { function: FuncId::new(0), block: BlockId::new(0), instruction: 6 })
        .unwrap();
    let target = catalog.branch_target(FuncId::new(0), BlockId::new(1)).unwrap();
    let checks = branching.branch_checks(&model, &current, &target, None).unwrap();
    let resolved = assembler
        .conversion(
            app("IRList", [c("IRScalar")]),
            app("ir_resolve", [current.machine(), checks.arguments]),
            list("IRScalar", &[]),
        )
        .unwrap();
    let arity = truth(&mut assembler, checks.arity);
    let branched = branching
        .branch_to(
            &mut assembler,
            &model,
            &current,
            &target,
            None,
            BranchPremises { condition: None, resolved, arity, before: valid },
        )
        .unwrap();
    prefix = assembler.concatenate(prefix, branched.run().clone()).unwrap();
    let returning = catalog
        .fetch(Coordinate { function: FuncId::new(0), block: BlockId::new(1), instruction: 0 })
        .unwrap();
    let dispatch = returning
        .step(&mut assembler, &model, branched.current(), branched.valid().clone())
        .unwrap();
    let finish = assembler
        .conversion(model.config_type(), dispatch.right().clone(), terminal(&Invocation::default()))
        .unwrap();
    let step = assembler.compose(dispatch, finish).unwrap();
    let run = assembler.one_step(&model, branched.current().running(&model), step).unwrap();
    let execution = assembler.concatenate(prefix, run).unwrap();
    let initialized_run = assembler
        .congruence(initialized.equality().clone(), model.config_type(), |state| {
            model.run(execution.fuel(), state)
        })
        .unwrap();
    let start = assembler
        .conversion(
            model.config_type(),
            model.run(&NatTerm::literal(8), initial(&model, 16)),
            initialized_run.left().clone(),
        )
        .unwrap();
    let middle = assembler
        .conversion(
            model.config_type(),
            initialized_run.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let complete = assembler.compose(start, initialized_run).unwrap();
    let complete = assembler.compose(complete, middle).unwrap();
    let complete = assembler.compose(complete, execution.equality().clone()).unwrap();
    let closed = scope.close(complete.term()).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no successful-evaluation or post-world premise may remain free"
    );
    // The eight-step proof shares whole contexts/worlds. Preserve that sharing
    // with the existing explicit DAG carrier; do not raise tree-decoder limits.
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}
