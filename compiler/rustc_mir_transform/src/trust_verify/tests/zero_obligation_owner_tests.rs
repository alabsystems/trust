//! Real owner lookup, fixpoint, candidacy merge and atomic installation seams.
//! Synthetic compiler ids are explicit; rendered labels never create identities.
use super::super::*;
use super::{blessing_candidate, blessing_identity, blessing_owner};

fn run(candidates: &[ZeroObligationBlessingCandidate], seeds: &[trust_types::CalleeIdentity]) -> FxHashSet<DefId> {
    let display = ["same::rendered".to_string()].into_iter().collect();
    zero_obligation_blessing_least_fixpoint(candidates, &display,
        &seeds.iter().copied().collect(), &FxHashSet::default(), &FxHashSet::default(),
        candidates.len().saturating_add(1)).unwrap()
}
fn state_with(candidates: &[ZeroObligationBlessingCandidate]) -> CrateVerificationState {
    let mut state = CrateVerificationState::default();
    for candidate in candidates {
        state.zero_obligation_undischarged_call_funcs.insert(candidate.owner);
        record_zero_obligation_blessing_candidate_for_owner(
            &mut state.zero_obligation_blessing_candidates, candidate.owner, Some(candidate.clone()));
    }
    state
}
fn install(state: &mut CrateVerificationState, snapshot: &[ZeroObligationBlessingCandidate], blessed: &FxHashSet<DefId>) -> bool {
    install_zero_obligation_blessings(state, snapshot, blessed,
        &FxHashSet::default(), &FxHashSet::default(), &FxHashSet::default())
}

#[test]
fn same_rendered_owners_keep_separate_negative_and_hypothesis_findings() {
    let first = blessing_owner(101);
    let second = DefId { krate: CrateNum::from_u32(8), index: first.index };
    let negative = [first, second].into_iter().collect();
    let hypotheses = [first].into_iter().collect();
    assert!(!zero_obligation_calls_undischarged_for_owner(Some(first), &negative, &hypotheses, true));
    assert!(zero_obligation_calls_undischarged_for_owner(Some(second), &negative, &hypotheses, true));
    assert!(zero_obligation_calls_undischarged_for_owner(Some(first), &negative, &hypotheses, false));
    assert!(zero_obligation_calls_undischarged_for_owner(None, &negative, &hypotheses, true));
}

#[test]
fn blessing_one_same_rendered_owner_does_not_clear_or_authenticate_the_other() {
    let first = blessing_candidate(101, "same::rendered", &[]);
    let second = blessing_candidate(102, "same::rendered",
        &[("missing::callee", Some(blessing_identity(103)))]);
    let candidates = [first.clone(), second.clone()];
    let mut state = state_with(&candidates);
    let blessed = run(&candidates, &[]);
    assert_eq!(blessed, [first.owner].into_iter().collect());
    assert!(install(&mut state, &candidates, &blessed));
    assert!(!state.zero_obligation_undischarged_call_funcs.contains(&first.owner));
    assert!(state.zero_obligation_undischarged_call_funcs.contains(&second.owner));
    assert!(state.panic_free_proven_identities.contains(&first.identity.unwrap()));
    assert!(!state.panic_free_proven_identities.contains(&second.identity.unwrap()));
    assert!(state.panic_free_proven_funcs.contains("same::rendered"), "display mirror is populated");
    let empty = FxHashSet::default();
    for identity in [None, second.identity] {
        assert!(!all_callee_keys_registry_or_bridge_total(&state.panic_free_proven_funcs,
            &state.panic_free_proven_identities, &empty, &empty, &empty, &empty, &empty, &empty,
            "caller", &[("same::rendered", identity.as_ref())], false));
    }
    assert!(all_callee_keys_registry_or_bridge_total(&state.panic_free_proven_funcs,
        &state.panic_free_proven_identities, &empty, &empty, &empty, &empty, &empty, &empty,
        "caller", &[("same::rendered", first.identity.as_ref())], false));
}

#[test]
fn owner_poison_is_permanent_and_does_not_poison_a_same_named_peer() {
    let first = blessing_candidate(111, "same::rendered", &[]);
    let second = blessing_candidate(112, "same::rendered", &[]);
    let mut candidates = FxHashMap::default();
    record_zero_obligation_blessing_candidate_for_owner(&mut candidates, first.owner, None);
    record_zero_obligation_blessing_candidate_for_owner(&mut candidates, first.owner, Some(first.clone()));
    record_zero_obligation_blessing_candidate_for_owner(&mut candidates, second.owner, Some(second.clone()));
    assert_eq!(candidates.get(&first.owner), Some(&None));
    assert_eq!(candidates.get(&second.owner), Some(&Some(second.clone())));
    assert_eq!(run(&[second.clone()], &[]), [second.owner].into_iter().collect());
    let wrong_owner = blessing_owner(113);
    record_zero_obligation_blessing_candidate_for_owner(&mut candidates, wrong_owner, Some(second));
    assert_eq!(candidates.get(&wrong_owner), Some(&None), "a mismatched record cannot borrow another owner");
}

#[test]
fn repeated_owner_walks_union_duties_and_intersect_typed_grants() {
    let mut first = blessing_candidate(121, "label::first", &[("callee::a", None)]);
    first.cell_set_total.insert("callee::a".to_string());
    let fresh = blessing_candidate(121, "label::changed", &[("callee::b", None)]);
    let merged = merge_zero_obligation_blessing_candidate(&Some(first.clone()), Some(fresh)).unwrap();
    assert_eq!(merged.callees.len(), 2);
    assert!(merged.cell_set_total.is_empty(), "one walk's typed permission cannot cover another");
    assert!(run(&[merged], &[]).is_empty());
    let changed_identity = ZeroObligationBlessingCandidate {
        identity: Some(trust_types::CalleeIdentity { substs_digest: [99, 100], ..first.identity.unwrap() }),
        ..first.clone()
    };
    assert!(merge_zero_obligation_blessing_candidate(&Some(first), Some(changed_identity)).is_none());
}

#[test]
fn snapshot_revocation_prevents_all_dependent_blessing_installations() {
    let leaf = blessing_candidate(131, "same::rendered", &[]);
    let caller = blessing_candidate(132, "same::rendered", &[("same::rendered", leaf.identity)]);
    let snapshot = [leaf.clone(), caller.clone()];
    let blessed = run(&snapshot, &[]);
    assert_eq!(blessed.len(), 2);
    let mut state = state_with(&snapshot);
    record_zero_obligation_blessing_candidate_for_owner(
        &mut state.zero_obligation_blessing_candidates, leaf.owner, None);
    assert!(!install(&mut state, &snapshot, &blessed));
    assert!(state.panic_free_proven_identities.is_empty());
    assert_eq!(state.zero_obligation_undischarged_call_funcs.len(), 2,
        "a dependent caller cannot ride a now-poisoned snapshot seed");
}

#[test]
fn snapshot_changed_call_surface_cannot_publish_a_partial_fixpoint() {
    let leaf = blessing_candidate(141, "same::rendered", &[]);
    let snapshot = [leaf.clone()];
    let blessed = run(&snapshot, &[]);
    let mut state = state_with(&snapshot);
    let changed = blessing_candidate(141, "same::rendered", &[("unproved::call", None)]);
    record_zero_obligation_blessing_candidate_for_owner(
        &mut state.zero_obligation_blessing_candidates, leaf.owner, Some(changed));
    assert!(!install(&mut state, &snapshot, &blessed));
    assert!(state.zero_obligation_undischarged_call_funcs.contains(&leaf.owner));
}

#[test]
fn an_unidentified_generic_item_cannot_seed_a_same_named_concrete_call() {
    let generic = ZeroObligationBlessingCandidate {
        identity: None, ..blessing_candidate(151, "same::rendered", &[])
    };
    let concrete = blessing_candidate(152, "caller::concrete",
        &[("same::rendered", Some(blessing_identity(151)))]);
    let blessed = run(&[generic.clone(), concrete.clone()], &[]);
    assert!(blessed.contains(&generic.owner));
    assert!(!blessed.contains(&concrete.owner));
}

#[test]
fn same_rendered_callee_with_different_instance_arguments_stays_unproved() {
    let expected = blessing_identity(161);
    let caller = blessing_candidate(162, "caller", &[("same::rendered", Some(expected))]);
    assert_eq!(run(&[caller.clone()], &[expected]), [caller.owner].into_iter().collect());
    for changed in [
        trust_types::CalleeIdentity { stable_crate_id: expected.stable_crate_id + 1, ..expected },
        trust_types::CalleeIdentity { def_index: expected.def_index + 1, ..expected },
        trust_types::CalleeIdentity { substs_digest: [expected.substs_digest[0] + 1, expected.substs_digest[1]], ..expected },
    ] {
        assert!(run(&[caller.clone()], &[changed]).is_empty());
    }
}

#[test]
fn promoted_source_does_not_borrow_its_item_owner_for_zero_row_authority() {
    let owner = blessing_owner(171);
    let mut source = rustc_middle::mir::MirSource::item(owner);
    assert_eq!(zero_obligation_source_owner(source), Some(owner));
    source.promoted = Some(rustc_middle::mir::Promoted::from_u32(0));
    assert_eq!(zero_obligation_source_owner(source), None);
}

#[test]
fn caller_typed_facts_with_same_rendering_remain_owner_keyed() {
    let (first, second) = (blessing_owner(181), blessing_owner(182));
    let mut state = CrateVerificationState::default();
    let mut facts = ZeroObligationTypedCallFacts::default();
    facts.cell_set_total.insert("same::callee".to_string());
    state.zero_obligation_typed_call_facts.insert(first, facts);
    state.zero_obligation_typed_call_facts.insert(second, ZeroObligationTypedCallFacts::default());
    let empty_identities: FxHashSet<trust_types::CalleeIdentity> = FxHashSet::default();
    let empty_names: FxHashSet<String> = FxHashSet::default();
    let display = ["same::callee".to_string()].into_iter().collect();
    for (owner, expected) in [(first, true), (second, false), (blessing_owner(183), false)] {
        let facts = zero_obligation_typed_facts_for_owner(&state, owner);
        assert_eq!(all_callee_keys_registry_or_bridge_total(
            &display, &empty_identities, &empty_names, &empty_names, &facts.cell_set_total,
            &facts.moved_value_total, &facts.tls_try_with_total, &facts.typed_self_total,
            "same::caller", &[("same::callee", None)], false,
        ), expected, "only this owner's fresh typed fact can grant the call");
    }
}
