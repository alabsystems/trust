//! Negative provenance survives removal of a previously resolved bundle body.
use super::*;
use crate::CallReachWithdrawals;

fn identity(index: u32) -> trust_types::CalleeIdentity {
    trust_types::CalleeIdentity { stable_crate_id: 7, def_index: index, substs_digest: [11, 13] }
}

fn caller(callee: &str, id: Option<trust_types::CalleeIdentity>, arity: usize) -> VerifiableFunction {
    let mut function = typed_absent_call(callee, vec![Ty::u64(); arity], Ty::Unit);
    let Terminator::Call { callee_identity, .. } = &mut function.body.blocks[0].terminator else {
        unreachable!()
    };
    *callee_identity = id;
    function
}

fn member(path: &str, arity: usize) -> VerifiableFunction {
    let mut function = caller("dep::unverified_body", None, arity);
    function.name = path.rsplit("::").next().unwrap().into();
    function.def_path = path.into();
    function
}

fn lower(caller: &VerifiableFunction, withdrawals: &CallReachWithdrawals) -> trust_ir::Module {
    let (Terminator::Call { func, .. } | Terminator::TailCall { func, .. }) =
        &caller.body.blocks[0].terminator else { unreachable!() };
    crate::lower::lower_to_trust_ir_functions_with_test_call_reach(
        "removed-member", std::slice::from_ref(caller),
        &[func.clone()].into_iter().collect(), withdrawals,
    ).expect("the original call keeps its continuation behind the fail-closed marker")
}

fn source_module(functions: &[VerifiableFunction]) -> trust_ir::Module {
    crate::lower::lower_to_trust_ir_functions_with_test_call_reach(
        "before-removal", functions,
        &functions.iter().map(|function| function.def_path.clone()).collect(),
        &CallReachWithdrawals::default(),
    ).expect("the complete source population lowers before removal")
}

fn withdraw(withdrawals: &mut CallReachWithdrawals, functions: &[VerifiableFunction], path: &str) {
    withdrawals.withdraw_removed_members(
        functions, &source_module(functions), &[path.into()].into_iter().collect(),
    ).expect("previous lowered calls bind to their exact original caller/block");
}

fn absent(module: &trust_ir::Module) -> Vec<&str> {
    module.proof_obligations.iter().filter(|row| row.description.starts_with(
        trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
    )).map(|row| row.description.as_str()).collect()
}

#[test]
fn removed_bundle_member_cannot_regain_compiler_total_credit() {
    let callee = "core::opaque_fixture::credited";
    let caller = caller(callee, Some(identity(1)), 1);
    let original = [caller.clone(), member(callee, 1)];
    let mut withdrawals = CallReachWithdrawals::default();
    assert!(absent(&lower(&caller, &withdrawals)).is_empty(), "control: absent total credit exists");
    withdraw(&mut withdrawals, &original, callee);
    let module = lower(&caller, &withdrawals);
    let rows = absent(&module);
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].contains("previously resolved bundled body"));
    assert!(rows[0].contains(callee));
    assert!(module.functions[0].blocks.iter().flat_map(|block| &block.body)
        .any(|node| matches!(node.inst, Inst::Assert { .. })));
}

#[test]
fn removed_bundle_member_keeps_typed_instance_keys_separate() {
    let callee = "core::opaque_fixture::credited";
    let original_caller = caller(callee, Some(identity(1)), 1);
    let mut withdrawals = CallReachWithdrawals::default();
    withdraw(&mut withdrawals, &[original_caller.clone(), member(callee, 1)], callee);
    assert_eq!(absent(&lower(&original_caller, &withdrawals)).len(), 1);
    assert!(absent(&lower(&caller(callee, Some(identity(2)), 1), &withdrawals)).is_empty());
    assert!(absent(&lower(&caller(callee, None, 1), &withdrawals)).is_empty());
}

#[test]
fn removed_bundle_member_bare_key_does_not_withdraw_identified_instances() {
    let callee = "core::opaque_fixture::credited";
    let original_caller = caller(callee, None, 1);
    let mut withdrawals = CallReachWithdrawals::default();
    withdraw(&mut withdrawals, &[original_caller.clone(), member(callee, 1)], callee);
    assert_eq!(absent(&lower(&original_caller, &withdrawals)).len(), 1);
    assert!(absent(&lower(&caller(callee, Some(identity(2)), 1), &withdrawals)).is_empty());
}

#[test]
fn removed_bundle_member_refined_alias_requires_the_declared_arity() {
    let callee = "core::opaque_fixture::credited";
    let alias = format!("{callee}::<u64>");
    for (arity, expected) in [(1, 1), (0, 0)] {
        let original_caller = caller(&alias, Some(identity(1)), arity);
        let mut withdrawals = CallReachWithdrawals::default();
        withdraw(&mut withdrawals, &[original_caller.clone(), member(callee, 1)], callee);
        assert_eq!(absent(&lower(&original_caller, &withdrawals)).len(), expected);
    }
}

#[test]
fn removed_bundle_member_exact_short_alias_and_tail_call_are_withdrawn() {
    let callee = "core::opaque_fixture::credited";
    let mut original_caller = caller("credited", Some(identity(1)), 1);
    let Terminator::Call { func, args, span, atomic, is_foreign, is_unsafe_sig,
        callee_identity, callee_key, .. } = original_caller.body.blocks[0].terminator.clone()
    else { unreachable!() };
    original_caller.body.blocks[0].terminator = Terminator::TailCall {
        func, args, span, atomic, is_foreign, is_unsafe_sig, callee_identity, callee_key,
    };
    original_caller.body.blocks.truncate(1);
    let mut withdrawals = CallReachWithdrawals::default();
    withdraw(&mut withdrawals, &[original_caller.clone(), member(callee, 1)], callee);
    let module = lower(&original_caller, &withdrawals);
    assert_eq!(absent(&module).len(), 1);
    assert!(module.functions[0].blocks[0].body.last()
        .is_some_and(|node| matches!(node.inst, Inst::Return { .. })));
}

#[test]
fn removed_bundle_member_withdrawal_is_cumulative_across_evictions() {
    let first = "core::opaque_fixture::first";
    let second = "core::opaque_fixture::second";
    let a = caller(first, Some(identity(1)), 1);
    let mut b = caller(second, Some(identity(2)), 1);
    b.name = "second_caller".into(); b.def_path = "test::second_caller".into();
    let original = [a.clone(), b.clone(), member(first, 1), member(second, 1)];
    let mut withdrawals = CallReachWithdrawals::default();
    withdraw(&mut withdrawals, &original, first);
    let mut candidate = withdrawals.clone();
    withdraw(&mut candidate, &[a.clone(), b.clone(), member(second, 1)], second);
    candidate.retain_callees(|_| false);
    assert_eq!(absent(&lower(&a, &candidate)).len(), 1);
    assert_eq!(absent(&lower(&b, &candidate)).len(), 1);
    assert!(absent(&lower(&b, &withdrawals)).is_empty(), "discarded candidate cannot change old context");
}

#[test]
fn removed_bundle_member_remains_visible_to_ledger_readers_after_census() {
    let callee = "core::opaque_fixture::credited";
    let original_caller = caller(callee, Some(identity(1)), 1);
    let mut withdrawals = CallReachWithdrawals::default();
    assert!(withdrawals.is_empty());
    withdrawals.insert(Some(identity(1)), callee, "ordinary call-reach reason".into());
    withdraw(&mut withdrawals, &[original_caller.clone(), member(callee, 1)], callee);
    assert!(withdrawals.reason(Some(&identity(1)), callee)
        .is_some_and(|reason| reason.contains("previously resolved bundled body")));
    withdrawals.retain_callees(|_| false);
    assert!(!withdrawals.is_empty(), "census credit cannot hide the evicted body");
    let reason = withdrawals.reason(Some(&identity(1)), callee)
        .expect("the actual lowering withdrawal is also visible to ledger readers");
    assert_eq!(withdrawals.entries().collect::<Vec<_>>(), vec![(callee, reason)]);
    assert_eq!(absent(&lower(&original_caller, &withdrawals)).len(), 1);
}

#[test]
fn removed_bundle_member_retained_and_unresolved_targets_do_not_gain_withdrawals() {
    let callee = "core::opaque_fixture::credited";
    let original_caller = caller(callee, Some(identity(1)), 1);
    let mut withdrawals = CallReachWithdrawals::default();
    withdraw(&mut withdrawals, &[original_caller.clone(), member(callee, 1)], "different::body");
    withdraw(&mut withdrawals, std::slice::from_ref(&original_caller), callee);
    assert_eq!(withdrawals, CallReachWithdrawals::default());
    assert_eq!(lower(&original_caller, &withdrawals).stable_digest(),
        lower(&original_caller, &CallReachWithdrawals::default()).stable_digest());
}

#[test]
fn removed_bundle_member_source_module_mismatches_refuse() {
    let callee = "core::opaque_fixture::credited";
    let original = [caller(callee, Some(identity(1)), 1), member(callee, 1)];
    let module = source_module(&original);
    let removed = [callee.into()].into_iter().collect();
    let mut changed_source = original.clone();
    changed_source[0].body.blocks[0].id = BlockId(99);
    assert!(CallReachWithdrawals::default()
        .withdraw_removed_members(&changed_source, &module, &removed).is_err());
    assert!(CallReachWithdrawals::default()
        .withdraw_removed_members(&original[..1], &module, &removed).is_err());
    let mut changed_module = module;
    changed_module.functions[0].id = trust_ir::FuncId::new(9);
    assert!(CallReachWithdrawals::default()
        .withdraw_removed_members(&original, &changed_module, &removed).is_err());
}

#[test]
fn removed_bundle_member_tracks_actual_typed_callable_dispatch() {
    let path = "test::typed_item";
    let shim = "core::ops::function::FnOnce::call_once";
    let mut original_caller = caller(shim, Some(identity(1)), 0);
    let Terminator::Call { args, .. } = &mut original_caller.body.blocks[0].terminator
    else { unreachable!() };
    *args = vec![
        Operand::Constant(ConstValue::CallableItem {
            def_path: path.into(), kind: CallableKind::FnDef,
            def_path_hash: callable_item_test_hash(),
        }),
        Operand::Constant(ConstValue::Unit),
    ];
    let original = [original_caller.clone(), member(path, 0)];
    let module = source_module(&original);
    assert!(module.functions[0].blocks.iter().flat_map(|block| &block.body)
        .any(|node| matches!(node.inst, Inst::Call { callee, .. } if callee.index() == 1)),
        "the original shim really resolves to the item body despite its different name");
    let mut withdrawals = CallReachWithdrawals::default();
    withdrawals.withdraw_removed_members(
        &original, &module, &[path.into()].into_iter().collect(),
    ).expect("the actual typed-dispatch call binds to its original shim site");
    let relowered = lower(&original_caller, &withdrawals);
    let rows = absent(&relowered);
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].contains(path) && rows[0].contains("previously resolved bundled body"));
    assert!(rows[0].contains(shim), "retain the original source call name too");
}

#[test]
fn first_withdrawn_source_call_names_only_withdrawn_keys() {
    // Trust (POISON-EVICTION-FALSE-PROOF-1): the poison loop's belt. A retained
    // call carrying a removed body's key would lower to a withdrawal row; the
    // ledger names it, and names no call with another key.
    let callee = "core::opaque_fixture::credited";
    let withdrawn = caller(callee, Some(identity(1)), 1);
    let other_instance = caller(callee, Some(identity(2)), 1);
    let mut withdrawals = CallReachWithdrawals::default();
    assert_eq!(withdrawals.first_withdrawn_source_call(std::slice::from_ref(&withdrawn)), None);
    withdraw(&mut withdrawals, &[withdrawn.clone(), member(callee, 1)], callee);
    assert_eq!(
        withdrawals.first_withdrawn_source_call(std::slice::from_ref(&withdrawn)),
        Some((withdrawn.def_path.as_str(), callee)),
    );
    assert_eq!(
        withdrawals.first_withdrawn_source_call(std::slice::from_ref(&other_instance)),
        None
    );
    // Agrees with lowering: the named call is the one that lowers fail-closed.
    assert_eq!(absent(&lower(&withdrawn, &withdrawals)).len(), 1);
    assert!(absent(&lower(&other_instance, &withdrawals)).is_empty());
}
