//! The retained MIR controls below exercise compiler-private reconciliation,
//! not a synthetic tcx qualification or source-authority mint. The harness must
//! bind the supplied extracts; live compiler instance selection is separate.
use super::*;

fn retained() -> Vec<trust_types::VerifiableFunction> {
    let directory = std::path::PathBuf::from(
        std::env::var_os("TRUST_STEP_BY_CONSTRUCTOR_EXTRACTS")
            .expect("supply source-bound retained u8_specialized/extracts"),
    );
    [
        "trust-mir-e04fcdb5a4e80ca6-11f3b595c55129e1.json",
        "trust-mir-a8d3b20d2ad8d04-26c4cafed7e3cfe7.json",
        "trust-mir-6c3bbfa8301979a2-e38b9c5e4e4780ed.json",
    ]
    .iter()
    .map(|name| {
        let mut function: trust_types::VerifiableFunction = serde_json::from_slice(
            &std::fs::read(directory.join(name)).expect("read retained MIR"),
        )
        .expect("decode MIR");
        function.name = function.def_path.clone();
        function
    })
    .collect()
}

fn modeled_facts(
    members: &[trust_types::VerifiableFunction],
) -> (BundledMemberSourceIdentityLedger, ConstructorQualifications) {
    let directory =
        std::path::PathBuf::from(std::env::var_os("TRUST_STEP_BY_CONSTRUCTOR_EXTRACTS").unwrap());
    let caller: trust_types::VerifiableFunction = serde_json::from_slice(
        &std::fs::read(directory.join("trust-mir-fe5b8b9e2f94644e-8f3912ea7c43c903.json")).unwrap(),
    )
    .unwrap();
    let mut ledger = BundledMemberSourceIdentityLedger::default();
    let mut qualifications = ConstructorQualifications::default();
    for (index, member) in members.iter().enumerate() {
        let identity = std::iter::once(&caller)
            .chain(members)
            .flat_map(|source| &source.body.blocks)
            .find_map(|block| match &block.terminator {
                trust_types::Terminator::Call { func, callee_identity, .. }
                    if func == &member.def_path =>
                {
                    *callee_identity
                }
                _ => None,
            })
            .expect("retained actual incoming call identity");
        record_bundled_member_source_identity(
            &mut ledger,
            member,
            Some(identity),
            false,
            false,
            false,
            // Trust (2026-09-29): not an authentic sysroot body.
            false,
        )
        .unwrap();
        qualifications.insert(
            bundled_member_source_identity_key(member).unwrap(),
            ConstructorQualification {
                identity,
                role: [
                    ConstructorMember::IteratorStepBy,
                    ConstructorMember::New,
                    ConstructorMember::RangeSetup,
                ][index],
                // Test input ONLY. Production must derive this from needs_drop on
                // its actual monomorphized rustc MIR, not these extracted names.
                no_drop_blocks: member
                    .body
                    .blocks
                    .iter()
                    .filter_map(|block| {
                        matches!(block.terminator, trust_types::Terminator::Drop { .. })
                            .then_some(block.id)
                    })
                    .collect(),
            },
        );
    }
    (ledger, qualifications)
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_plan_keeps_panic_shared_assert_and_drop_as_three_separate_source_sites() {
    let members = retained();
    let (ledger, qualifications) = modeled_facts(&members);
    let plan = plan_for_member(&members[0], &members, &ledger, &qualifications).unwrap();
    assert_eq!(plan.sites.len(), 3);
    assert_eq!(
        plan.sites
            .iter()
            .filter(|site| matches!(site.source, ConstructorSourceSite::NoDrop { .. }))
            .count(),
        1
    );
    let setup =
        plan.sites.iter().find(|site| site.owner_role == ConstructorMember::RangeSetup).unwrap();
    assert_eq!(setup.path.len(), 2);
    let ConstructorSourceSite::Safety(site) = &setup.source else {
        panic!("real setup Assert required")
    };
    assert_eq!(site.guarded_operations.len(), 2, "one source Assert covers both Div and Rem");
    // The canonical payload `reconcile_bundle` compares is deterministic: the
    // same plan serializes to the identical ordered inventory every time.
    let payload = |sites: &[ConstructorSiteRequirement]| {
        sites.iter().map(ConstructorSiteRequirement::to_json).collect::<Vec<_>>()
    };
    assert_eq!(payload(&plan.sites), payload(&plan.sites));
    assert_eq!(plan.summary(&members[0]).unwrap().preconditions.len(), 2);
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn only_a_terminal_panic_is_charged_locally_instead_of_requiring_a_child_body() {
    let members = retained();
    let ctor = &members[1];
    let panic_block = ctor
        .body
        .blocks
        .iter()
        .find(|block| {
            matches!(&block.terminator, trust_types::Terminator::Call {
            func, target: None, ..
        } if func == "core::panicking::panic")
        })
        .expect("actual retained constructor panic terminal");
    let sites = trust_ir_bridge::bundled_constructor_local_safety_sites(ctor).unwrap();
    assert!(sites.iter().any(|site| site.block == panic_block.id
        && matches!(&site.requirement, Formula::Implies(_, requirement)
            if **requirement == Formula::Bool(false))));
    let calls = trust_ir_bridge::bundled_constructor_call_sites(ctor).unwrap();
    assert!(calls.iter().all(|call| call.block != panic_block.id));
    let return_block = ctor
        .body
        .blocks
        .iter()
        .find(|block| matches!(&block.terminator, trust_types::Terminator::Return))
        .unwrap()
        .id;

    for returning_panic in [false, true] {
        let mut mutated = members.clone();
        let block =
            mutated[1].body.blocks.iter_mut().find(|block| block.id == panic_block.id).unwrap();
        let trust_types::Terminator::Call { func, target, .. } = &mut block.terminator else {
            unreachable!()
        };
        if returning_panic {
            *target = Some(return_block);
            let calls = trust_ir_bridge::bundled_constructor_call_sites(&mutated[1]).unwrap();
            assert!(
                calls.iter().any(|call| call.block == panic_block.id),
                "a normal-return edge cannot use the charged-terminal exception"
            );
        } else {
            *func = "external::ordinary_diverging_call".into();
            assert!(
                trust_ir_bridge::bundled_constructor_call_sites(&mutated[1]).is_err(),
                "an unknown diverging call is not a recognized panic source site"
            );
        }
        let (ledger, qualifications) = modeled_facts(&mutated);
        let error = plan_for_member(&mutated[0], &mutated, &ledger, &qualifications)
            .err()
            .expect("unqualified call must keep the whole summary refused");
        if returning_panic {
            assert!(error.contains("call body is absent"), "{error}");
        } else {
            assert!(error.contains("unsupported constructor call effect"), "{error}");
        }
    }
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn retained_plan_requires_exact_body_identity_qualification_and_drop_population() {
    let members = retained();
    let (ledger, qualifications) = modeled_facts(&members);
    assert!(plan_for_member(&members[0], &members[..2], &ledger, &qualifications).is_err());
    let mut missing = qualifications.clone();
    missing.remove(&bundled_member_source_identity_key(&members[2]).unwrap());
    assert!(plan_for_member(&members[0], &members, &ledger, &missing).is_err());
    for duplicate in [false, true] {
        let mut bad_drop = qualifications.clone();
        let fact =
            bad_drop.get_mut(&bundled_member_source_identity_key(&members[1]).unwrap()).unwrap();
        if duplicate {
            fact.no_drop_blocks.push(fact.no_drop_blocks[0]);
        } else {
            fact.no_drop_blocks.clear();
        }
        assert!(plan_for_member(&members[0], &members, &ledger, &bad_drop).is_err());
    }
    let mut wrong_id = qualifications.clone();
    wrong_id
        .get_mut(&bundled_member_source_identity_key(&members[2]).unwrap())
        .unwrap()
        .identity
        .def_index ^= 1;
    assert!(plan_for_member(&members[0], &members, &ledger, &wrong_id).is_err());
    let mut modified = members.clone();
    modified[2].body.blocks[0].stmts.push(trust_types::Statement::Nop);
    assert!(
        plan_for_member(&modified[0], &modified, &ledger, &qualifications).is_err(),
        "source changes require a fresh exact qualification"
    );
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn two_same_instance_root_calls_keep_four_safety_charges_and_two_no_drop_dispositions() {
    use trust_types::{BasicBlock, BlockId, ConstValue, Operand, Place, Terminator};
    let members = retained();
    let (ledger, qualifications) = modeled_facts(&members);
    let plan = plan_for_member(&members[0], &members, &ledger, &qualifications).unwrap();
    let mut root = members[0].clone();
    root.name = "constructor_test::two_sites".into();
    root.def_path = root.name.clone();
    let mut call = root.body.blocks[0].terminator.clone();
    let Terminator::Call { func, callee_identity, target, .. } = &mut call else {
        panic!("actual outer call")
    };
    *func = members[0].name.clone();
    *callee_identity = Some(plan.entry_identity);
    *target = Some(BlockId(3));
    let mut zero = call.clone();
    let Terminator::Call { args, .. } = &mut zero else { unreachable!() };
    args[1] = Operand::Constant(ConstValue::Uint(0, 64));
    root.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(1))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: root.span.clone(),
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: zero },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: call },
        BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
    ];
    let charges = plan.root_charges(&root, &members[0]).unwrap();
    assert_eq!(
        charges.len(),
        4,
        "two actual source safety checks per invocation, no tautological proof credit"
    );
    assert_eq!(charges.iter().filter(|charge| charge.root_block == BlockId(1)).count(), 2);
    assert_eq!(charges.iter().filter(|charge| charge.root_block == BlockId(2)).count(), 2);
    assert_eq!(
        charges
            .iter()
            .filter(|charge| matches!(charge.site.source, ConstructorSourceSite::NoDrop { .. }))
            .count(),
        0
    );
    let inventory = plan.root_sites(&root).unwrap();
    assert_eq!(inventory.len(), 6);
    assert_eq!(inventory.iter().filter(|(_, _, _, site)| site.requirement.is_none()).count(), 2);
    assert_ne!(
        charges[0].vc.formula, charges[2].vc.formula,
        "actual zero and guarded nonzero branches must not share one formula"
    );
    if let Some(path) = std::env::var_os("TRUST_CONSTRUCTOR_PRIVATE_CALLER_QUERIES") {
        let file = std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        let vcs: Vec<_> = charges.iter().map(|charge| charge.vc.clone()).collect();
        let dispositions: Vec<_> = inventory
            .iter()
            .filter(|(_, _, _, site)| site.requirement.is_none())
            .map(|(block, arguments, _, site)| {
                serde_json::json!({
                    "root_block": block, "root_arguments": arguments, "site": site.to_json(),
                })
            })
            .collect();
        serde_json::to_writer_pretty(
            file,
            &serde_json::json!({
                "root": root, "vcs": vcs, "no_drop_dispositions": dispositions,
            }),
        )
        .unwrap();
    }
    let Terminator::Call { callee_identity, .. } = &mut root.body.blocks[2].terminator else {
        unreachable!()
    };
    *callee_identity = None;
    assert!(
        plan.root_charges(&root, &members[0]).is_err(),
        "second same-name call cannot borrow first site's identity"
    );
}

fn public_fixture() -> (
    trust_types::VerifiableFunction,
    Vec<trust_types::VerifiableFunction>,
    BundledMemberSourceIdentityLedger,
    Vec<VerificationCondition>,
    trust_verifier_api::TrustContractBundle,
) {
    let members = retained();
    let (mut ledger, qualifications) = modeled_facts(&members);
    for member in &members {
        record_qualification(
            &mut ledger,
            member,
            qualifications[&bundled_member_source_identity_key(member).unwrap()].clone(),
        )
        .unwrap();
    }
    let plan = plan_for_member(&members[0], &members, &ledger, &qualifications).unwrap();
    let mut root = members[0].clone();
    // Actual extractor names and full definition paths are not interchangeable.
    root.name = "public_entry".into();
    root.def_path = "constructor_test::public_entry".into();
    let trust_types::Terminator::Call { func, callee_identity, .. } =
        &mut root.body.blocks[0].terminator
    else {
        unreachable!()
    };
    *func = members[0].name.clone();
    *callee_identity = Some(plan.entry_identity);
    let vcs: Vec<_> = plan
        .root_charges(&root, &members[0])
        .unwrap()
        .into_iter()
        .map(|charge| charge.vc)
        .collect();
    let bundle = trust_mir_extract::function_to_verifier_api_bundle_with_compiler_identity(
        &root,
        &trust_types::CompilerContractBundle::new(vec![]),
        &vcs,
        "constructor_test",
        17,
        Some(64),
    );
    let mut population = vec![root.clone()];
    population.extend(members);
    (root, population, ledger, vcs, bundle)
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn public_constructor_charges_keep_exact_source_paths_and_unique_ids() {
    let (root, members, ledger, vcs, mut bundle) = public_fixture();
    let bindings = reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).unwrap();
    assert_eq!(bindings.members.len(), 3);
    assert_eq!(bindings.charges.len(), 2);
    assert_eq!(
        bindings.charges.iter().map(|charge| charge.vc_index).collect::<FxHashSet<_>>().len(),
        2
    );
    bindings.attach(&mut bundle).unwrap();
    assert_eq!(
        bundle
            .obligations
            .iter()
            .filter(|row| row
                .metadata
                .iter()
                .any(|entry| entry.key == CONSTRUCTOR_SOURCE_SITE_METADATA))
            .count(),
        2
    );
    assert!(reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).is_ok());
    // A metadata payload cannot select a different member or call path, even
    // when its already-authenticated scalar VC formula is unchanged.
    let entry = bundle
        .obligations
        .iter_mut()
        .flat_map(|row| &mut row.metadata)
        .find(|entry| entry.key == CONSTRUCTOR_SOURCE_SITE_METADATA)
        .unwrap();
    let mut payload: serde_json::Value = serde_json::from_str(&entry.value).unwrap();
    payload["source_site"]["owner_source_digest"] = serde_json::json!("wrong-owner");
    entry.value = payload.to_string();
    assert!(reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).is_err());
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn public_constructor_gate_rejects_dropped_duplicated_and_unowned_charges() {
    let (root, members, ledger, vcs, bundle) = public_fixture();
    for index in 0..vcs.len() {
        let mut missing = vcs.clone();
        missing.remove(index);
        assert!(reconcile_bundle(&root, &members, &ledger, &missing, &bundle).is_err());
        let mut missing_public = bundle.clone();
        missing_public.obligations.remove(index);
        assert!(reconcile_bundle(&root, &members, &ledger, &vcs, &missing_public).is_err());
    }
    let mut duplicate = bundle.clone();
    duplicate.obligations.push(duplicate.obligations[0].clone());
    assert!(reconcile_bundle(&root, &members, &ledger, &vcs, &duplicate).is_err());
    let mut wrong_identity = members.clone();
    let trust_types::Terminator::Call { callee_identity, .. } =
        &mut wrong_identity[0].body.blocks[0].terminator
    else {
        unreachable!()
    };
    *callee_identity = None;
    assert!(reconcile_bundle(&wrong_identity[0], &wrong_identity, &ledger, &vcs, &bundle).is_err());
    let mut outside = members.clone();
    let mut extra = root.clone();
    extra.name = "constructor_test::uncharged_member".into();
    extra.def_path = extra.name.clone();
    outside.push(extra);
    assert!(reconcile_bundle(&root, &outside, &ledger, &vcs, &bundle).is_err());
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn constructor_gate_preserves_legacy_refusal_until_complete_public_reconciliation() {
    let (root, members, ledger, vcs, bundle) = public_fixture();
    assert!(
        ensure_bundled_member_asserts_exactly_charged(
            &root,
            &members,
            &ledger,
            &vcs,
            &FxHashSet::default(),
        )
        .is_err()
    );
    let bindings = reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).unwrap();
    assert!(
        ensure_bundled_member_asserts_exactly_charged(
            &root,
            &members,
            &ledger,
            &vcs,
            &bindings.members,
        )
        .is_ok()
    );
    let mut no_setup = members.clone();
    no_setup.pop();
    assert!(reconcile_bundle(&root, &no_setup, &ledger, &vcs, &bundle).is_err());
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn no_drop_disposition_has_no_public_proof_credit_but_cannot_be_dropped_or_rewritten() {
    let (root, members, ledger, vcs, mut bundle) = public_fixture();
    let bindings = reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).unwrap();
    let inventory: serde_json::Value =
        serde_json::from_str(bindings.inventory_payload.as_ref().unwrap()).unwrap();
    assert_eq!(inventory["source_sites"].as_array().unwrap().len(), 3);
    assert_eq!(inventory["public_safety_charges"].as_array().unwrap().len(), 2);
    let no_drop: Vec<_> = inventory["source_sites"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|site| site["requires_public_vc"] == false)
        .collect();
    assert_eq!(no_drop.len(), 1);
    assert!(no_drop[0]["source_site"]["requirement"].is_null());
    assert_eq!(no_drop[0]["source_site"]["source"]["proof_credit"], false);
    bindings.attach(&mut bundle).unwrap();
    for duplicate in [false, true] {
        let mut mutant = bundle.clone();
        let metadata = mutant.obligations[0]
            .metadata
            .iter_mut()
            .find(|entry| entry.key == CONSTRUCTOR_SOURCE_INVENTORY_METADATA)
            .unwrap();
        let mut value: serde_json::Value = serde_json::from_str(&metadata.value).unwrap();
        let sites = value["source_sites"].as_array_mut().unwrap();
        let position = sites.iter().position(|site| site["requires_public_vc"] == false).unwrap();
        if duplicate {
            sites.push(sites[position].clone());
        } else {
            sites.remove(position);
        }
        metadata.value = value.to_string();
        assert!(reconcile_bundle(&root, &members, &ledger, &vcs, &mutant).is_err());
    }
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn intrinsic_machine_bounds_are_exact_type_facts_not_authored_assumption_authority() {
    let member = retained().remove(0);
    assert!(only_exact_intrinsic_integer_bounds(&member));
    for mutation in 0..6 {
        let mut mutant = member.clone();
        match mutation {
            0 => {
                mutant.body.locals.iter_mut().find(|local| local.index == 2).unwrap().ty =
                    trust_types::Ty::Int { width: 32, signed: false }
            }
            1 => {
                mutant.body.locals.iter_mut().find(|local| local.index == 2).unwrap().ty =
                    trust_types::Ty::Int { width: 64, signed: true }
            }
            2 => {
                mutant.body.locals.iter_mut().find(|local| local.index == 2).unwrap().name =
                    Some("different_formal".into())
            }
            3 => mutant.preconditions.push(Formula::Bool(false)),
            4 => {
                let Formula::And(bounds) = &mut mutant.preconditions[0] else { unreachable!() };
                let Formula::Ge(_, lower) = &mut bounds[0] else { unreachable!() };
                **lower = Formula::Int(1);
            }
            5 => {
                mutant.body.locals.iter_mut().find(|local| local.index == 0).unwrap().name =
                    Some("step".into())
            }
            _ => unreachable!(),
        }
        assert!(!only_exact_intrinsic_integer_bounds(&mutant), "mutation {mutation}");
    }
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn public_attachment_rechecks_the_full_row_and_disposition_carriers() {
    for change_inventory in [false, true] {
        let (root, members, ledger, vcs, mut bundle) = public_fixture();
        let bindings = reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).unwrap();
        if change_inventory {
            bundle.obligations[0].metadata.push(trust_verifier_api::MetadataEntry {
                key: CONSTRUCTOR_SOURCE_INVENTORY_METADATA.into(),
                value: "changed-after-reconciliation".into(),
            });
        } else {
            bundle.obligations[0].description.push_str(" changed after reconciliation");
        }
        assert!(bindings.attach(&mut bundle).is_err());
    }
}

#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn only_completely_unmentioned_shared_reference_declarations_are_inert() {
    let member = retained().remove(2);
    let sites = trust_ir_bridge::bundled_constructor_local_safety_sites(&member).unwrap();
    assert!(validate_member_effect_inventory(&member, &sites, &[]).is_ok());
    for index in [3, 6, 7, 8, 9] {
        assert!(!constructor_mentions_local(&member, index));
        let mut mentioned = member.clone();
        mentioned.body.blocks[0].stmts.insert(0, trust_types::Statement::StorageLive(index));
        assert!(constructor_mentions_local(&mentioned, index));
        assert!(validate_member_effect_inventory(&mentioned, &sites, &[]).is_err());
        let mut mutable = member.clone();
        let trust_types::Ty::Ref { mutable: flag, .. } =
            &mut mutable.body.locals.iter_mut().find(|local| local.index == index).unwrap().ty
        else {
            unreachable!()
        };
        *flag = true;
        assert!(validate_member_effect_inventory(&mutable, &sites, &[]).is_err());
    }
}

/// gate-rca deadline (2026-10-17): `trust_types::verify_budget`'s consumer discipline in
/// the reconciliation — a caller-side regeneration made while the ambient budget is
/// exhausted (here: a passed deadline, as the native share's is once it passes) is
/// discarded, never charged. Control: the same reconciliation under a live budget
/// succeeds, so the refusal is the budget's.
#[test]
#[ignore = "requires source-bound retained compiler extracts"]
fn reconciliation_discards_a_regeneration_made_over_budget() {
    let (root, members, ledger, vcs, bundle) = public_fixture();
    {
        let past = std::time::Instant::now()
            .checked_sub(std::time::Duration::from_millis(1))
            .unwrap_or_else(std::time::Instant::now);
        let _spent = trust_types::verify_budget::VerifyBudgetGuard::install(Some(past), u64::MAX);
        assert_eq!(
            reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).err().as_deref(),
            Some(CONSTRUCTOR_REGENERATION_OVER_BUDGET)
        );
    }
    let _live = trust_types::verify_budget::VerifyBudgetGuard::install(None, u64::MAX);
    assert!(reconcile_bundle(&root, &members, &ledger, &vcs, &bundle).is_ok());
}
