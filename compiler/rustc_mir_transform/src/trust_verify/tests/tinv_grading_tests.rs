//! Trust (TINV step 10.4): grading a row that carries a type-invariant premise — the
//! `TypeInvariantComposed` mint (`mint_type_invariant_composed_authorities`), the cap pass
//! (`cap_type_invariant_authorities`), the composer exclusions and the run-level ∧I gate.
//! Step 10.7: the token now reads proved WITH its disclosure on every surface (TINV-28
//! amended); the composer exclusions stay.

use std::collections::{BTreeMap, BTreeSet};

use trust_vcgen::type_invariant::TinvAssumedRow;

use super::super::type_invariant::{TinvRowDisclosure, TinvRowStatus, run_level_and_i_gate};
use super::super::*;
use super::{authority_test_proved, s1_test_eligibility, s1_test_strict_result, test_vc};

const TY: &str = "c::P";

fn tag(id: u32) -> String {
    trust_types::type_invariant_assume_tag(TY, id)
}

/// The tag map a use set publishing conjuncts `ids` of `TY` hands the disclosure.
fn published(ids: &[u32]) -> BTreeMap<String, (String, u32)> {
    ids.iter().map(|id| (tag(*id), (TY.to_string(), *id))).collect()
}

/// A row whose formula is `And([fact.., a ∧ ¬a])`, `fact` = `And([tag, x <= 5])` per
/// tag in `tags` (the use-site shape), at line `line`.
fn row(line: u32, tags: &[String]) -> (VerificationCondition, VerificationResult) {
    let mut vc = test_vc(line);
    let atom = trust_types::Formula::Var(format!("a{line}"), trust_types::Sort::Bool);
    let mut parts: Vec<trust_types::Formula> = tags
        .iter()
        .map(|t| {
            trust_types::Formula::And(vec![
                trust_types::Formula::Var(t.clone(), trust_types::Sort::Bool),
                trust_types::Formula::Le(
                    Box::new(trust_types::Formula::Var("x".into(), trust_types::Sort::Int)),
                    Box::new(trust_types::Formula::Int(5)),
                ),
            ])
        })
        .collect();
    parts.push(trust_types::Formula::And(vec![
        atom.clone(),
        trust_types::Formula::Not(Box::new(atom)),
    ]));
    vc.formula = trust_types::Formula::And(parts);
    (vc, authority_test_proved())
}

/// The generation record of `vc` with `tags` (the safety walk's record).
fn record(vc: &VerificationCondition, tags: &[String]) -> TinvAssumedRow {
    TinvAssumedRow {
        def_path: "test::f".into(),
        kind: vc.kind.clone(),
        location: vc.location.clone(),
        tags: tags.iter().cloned().collect(),
    }
}

/// The S1 receipts of `results` (every row eligible, every re-solve strict-UNSAT).
fn receipts(
    results: &[(VerificationCondition, VerificationResult)],
) -> Vec<Option<SolverRevalidationReceipt>> {
    let eligibilities: Vec<_> = results
        .iter()
        .enumerate()
        .map(|(index, (vc, _))| Some(s1_test_eligibility(index, vc)))
        .collect();
    revalidate_all_solver_proofs_with(
        results,
        &eligibilities,
        &vec![None; results.len()],
        None,
        std::time::Instant::now,
        |formula, _| Ok(s1_test_strict_result(formula)),
    )
    .receipts
}

/// The full lane's mint: the generic rungs, then the composed rung.
fn mint(
    results: &[(VerificationCondition, VerificationResult)],
    disclosure: &TinvRowDisclosure,
) -> Vec<Option<ResultProofAuthority>> {
    let receipts = receipts(results);
    let mut authorities = build_result_proof_authorities_with_revalidations(
        results,
        &[],
        None,
        &vec![None; results.len()],
        &receipts,
    );
    mint_type_invariant_composed_authorities(results, &[], &receipts, &mut authorities, disclosure);
    authorities
}

fn grade(
    results: &[(VerificationCondition, VerificationResult)],
    authorities: &[Option<ResultProofAuthority>],
    index: usize,
) -> Option<(TrustStatus, TrustProofStrength)> {
    let (vc, result) = &results[index];
    trust_disposition_for_authority(authorities[index].as_ref(), index, vc, result, None)
}

#[test]
fn a_tagged_row_is_composed_trusted_deductive_and_conditional_when_the_channels_agree() {
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags), row(2, &[])];
    let disclosure =
        TinvRowDisclosure::from_parts(Some(published(&[0])), vec![record(&results[0].0, &tags)]);
    assert_eq!(
        disclosure.row_status(&results[0].0),
        TinvRowStatus::Composable([(TY.to_string(), 0)].into_iter().collect())
    );
    assert_eq!(disclosure.row_status(&results[1].0), TinvRowStatus::Clear);
    assert!(disclosure.body_carries_premise());

    let authorities = mint(&results, &disclosure);
    let Some(ResultProofAuthority::TypeInvariantComposed { assumes, .. }) = &authorities[0] else {
        panic!("{:?}", authorities[0]);
    };
    assert_eq!(assumes, &[(TY.to_string(), 0)].into_iter().collect::<BTreeSet<_>>());
    assert_eq!(
        grade(&results, &authorities, 0),
        Some((TrustStatus::Trusted, TrustProofStrength::Deductive))
    );
    let (vc, result) = &results[0];
    let auth = authorities[0].as_ref().unwrap();
    // TINV-28 amended (step 10.7): the row reads proved, and only together with its
    // rendered premise; it is never an unconditional (all-input) proof.
    assert!(auth.is_static_proof_for(0, vc, result, None), "a disclosed Trusted proof");
    assert!(auth.permits_static_proved_transport_for(0, vc, result, None));
    assert_eq!(
        auth.type_invariant_disclosure_for(0, vc, result, None),
        Some(&[trust_types::type_invariant_assumes_label(TY, 0)][..])
    );
    assert!(!auth.is_unconditional_static_proof_for(0, vc, result, None), "never unconditional");
    assert!(!auth.is_kernel_proof_for(0, vc, None));
    assert!(auth.kernel_evidence_for(0, vc, None).is_none(), "no kernel term");
    assert!(!auth.is_exact_source_clause_body_proof_for(0, vc, result, None));
    assert_eq!(pf_authority_name(auth), "TypeInvariantComposed");
    // The untagged sibling keeps its ordinary S1 grade.
    assert!(matches!(authorities[1], Some(ResultProofAuthority::SolverRevalidated { .. })));
}

#[test]
fn a_tagged_row_gets_no_authority_without_an_installed_set_or_a_matching_record() {
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags)];
    let refused = |disclosure: TinvRowDisclosure| {
        let authorities = mint(&results, &disclosure);
        assert!(authorities[0].is_none(), "{:?}", authorities[0]);
        assert!(matches!(disclosure.row_status(&results[0].0), TinvRowStatus::Refused(_)));
    };
    // The generic mint alone gives a tagged row nothing (the production default).
    let generic = build_result_proof_authorities_with_revalidations(
        &results,
        &[],
        None,
        &[None],
        &receipts(&results),
    );
    assert!(generic[0].is_none(), "{:?}", generic[0]);
    // No set installed.
    refused(TinvRowDisclosure::default());
    refused(TinvRowDisclosure::from_parts(None, vec![record(&results[0].0, &tags)]));
    // A set, but no record of the row (a tag with no installation).
    refused(TinvRowDisclosure::from_parts(Some(published(&[0])), vec![]));
    // The record names a different tag set.
    refused(TinvRowDisclosure::from_parts(
        Some(published(&[0, 1])),
        vec![record(&results[0].0, &[tag(0), tag(1)])],
    ));
    // The tag names no published conjunct.
    refused(TinvRowDisclosure::from_parts(
        Some(published(&[1])),
        vec![record(&results[0].0, &tags)],
    ));
}

/// The tag-separation tripwire: the instance kept, the tag gone from the formula, the
/// generation record intact. No authority, from any rung.
#[test]
fn a_row_whose_tag_was_stripped_but_whose_fact_was_installed_mints_nothing() {
    let tags = vec![tag(0)];
    let (installed, _) = row(1, &tags);
    let mut stripped = row(1, &[]);
    // The same instance, without its tag.
    let trust_types::Formula::And(parts) = &installed.formula else { unreachable!() };
    let trust_types::Formula::And(fact) = &parts[0] else { unreachable!() };
    let trust_types::Formula::And(core) = &stripped.0.formula else { unreachable!() };
    stripped.0.formula = trust_types::Formula::And(vec![fact[1].clone(), core[0].clone()]);
    let results = vec![stripped];
    let disclosure =
        TinvRowDisclosure::from_parts(Some(published(&[0])), vec![record(&installed, &tags)]);
    assert!(matches!(disclosure.row_status(&results[0].0), TinvRowStatus::Refused(_)));
    // The generic mint WOULD grade it (it is untagged) ...
    let generic = build_result_proof_authorities_with_revalidations(
        &results,
        &[],
        None,
        &[None],
        &receipts(&results),
    );
    assert!(matches!(generic[0], Some(ResultProofAuthority::SolverRevalidated { .. })));
    // ... and the composed rung, which reads the generation record, strips it.
    assert!(mint(&results, &disclosure)[0].is_none());
    // So does the cap, over any authority a later lane might have put there.
    let mut authorities = generic;
    assert_eq!(cap_type_invariant_authorities(&results, &mut authorities, &disclosure), 1);
    assert!(authorities[0].is_none());
}

#[test]
fn the_cap_keeps_only_the_matching_composed_token_on_premised_rows() {
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags), row(2, &[]), row(3, &[])];
    let disclosure =
        TinvRowDisclosure::from_parts(Some(published(&[0])), vec![record(&results[0].0, &tags)]);
    let mut authorities = mint(&results, &disclosure);
    assert!(matches!(authorities[0], Some(ResultProofAuthority::TypeInvariantComposed { .. })));
    // A forged ordinary S1 token on the tagged row, and a composed token moved onto a
    // clear row, are both stripped; the clear row's own S1 token stays.
    let forged_s1 = match &authorities[1] {
        Some(ResultProofAuthority::SolverRevalidated { receipt, .. }) => {
            ResultProofAuthority::SolverRevalidated {
                row: exact_result_row_identity(0, &results[0].0).unwrap(),
                receipt: receipt.clone(),
            }
        }
        other => panic!("{other:?}"),
    };
    let moved = match &authorities[0] {
        Some(ResultProofAuthority::TypeInvariantComposed { receipt, assumes, .. }) => {
            ResultProofAuthority::TypeInvariantComposed {
                row: exact_result_row_identity(2, &results[2].0).unwrap(),
                receipt: receipt.clone(),
                assumes: assumes.clone(),
                disclosure: vec![trust_types::type_invariant_assumes_label(TY, 0)],
            }
        }
        other => panic!("{other:?}"),
    };
    let kept = authorities.clone();
    assert_eq!(cap_type_invariant_authorities(&results, &mut authorities, &disclosure), 0);
    assert_eq!(format!("{authorities:?}"), format!("{kept:?}"), "a minted set is left alone");
    authorities[0] = Some(forged_s1);
    authorities[2] = Some(moved);
    assert_eq!(cap_type_invariant_authorities(&results, &mut authorities, &disclosure), 2);
    assert!(authorities[0].is_none() && authorities[2].is_none());
    assert!(matches!(authorities[1], Some(ResultProofAuthority::SolverRevalidated { .. })));
}

/// TINV-27 at the registry predicates: a body holding a composed row is never an
/// unconditional all-input proof, so the interprocedural closure cannot take it.
#[test]
fn a_composed_row_is_never_an_unconditional_premise() {
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags)];
    let disclosure =
        TinvRowDisclosure::from_parts(Some(published(&[0])), vec![record(&results[0].0, &tags)]);
    let authorities = mint(&results, &disclosure);
    let (vc, result) = &results[0];
    let auth = authorities[0].as_ref().expect("minted");
    // Step 10.7: a disclosed static proof of its own row, never an unconditional one.
    assert!(auth.is_static_proof_for(0, vc, result, None));
    assert!(!auth.is_unconditional_static_proof_for(0, vc, result, None));
    assert!(!result_row_has_e4_e5_proof_authority(0, vc, result, &[], &authorities));
}

/// Without any install, a body's grading is untouched: the cap strips nothing and the
/// body carries no premise.
#[test]
fn an_uninstalled_disclosure_changes_nothing_on_untagged_rows() {
    let results = vec![row(1, &[]), row(2, &[])];
    let disclosure = TinvRowDisclosure::default();
    assert!(!disclosure.body_carries_premise());
    let mut authorities = mint(&results, &disclosure);
    let before = format!("{authorities:?}");
    assert!(authorities.iter().all(Option::is_some));
    assert_eq!(cap_type_invariant_authorities(&results, &mut authorities, &disclosure), 0);
    assert_eq!(format!("{authorities:?}"), before);
}

/// TINV-22: publication is all-or-nothing per run.
#[test]
fn the_and_i_gate_is_run_level() {
    let ok: Vec<(&str, Result<(), String>)> = vec![("a", Ok(())), ("b", Ok(()))];
    assert_eq!(run_level_and_i_gate(&ok), Ok(()));
    let one_fails = vec![("a", Ok(())), ("b", Err("witness".to_string())), ("c", Ok(()))];
    assert_eq!(run_level_and_i_gate(&one_fails), Err((&"b", "witness")));
    let none: Vec<(&str, Result<(), String>)> = Vec::new();
    assert_eq!(run_level_and_i_gate(&none), Ok(()));
}

/// Review fold-in 1: a grounded whole-function panic-freedom catch-all whose premise
/// sibling rests on a type-invariant fact (the refute-lane shape: the catch-all's own
/// grounded formula is untagged and kernel-certified, the sibling is tagged and minted
/// `TypeInvariantComposed`) loses its token. `GroundedPanicFreedomDerivation` cannot
/// disclose the TINV premise it would inherit. Control: an untagged sibling with its
/// ordinary S1 authority grades the catch-all `GroundedPanicFreedomDerivation`.
#[test]
fn a_grounded_catchall_over_a_tinv_premised_sibling_loses_its_token() {
    let contradiction = trust_types::Formula::Eq(
        Box::new(trust_types::Formula::Int(0)),
        Box::new(trust_types::Formula::Int(1)),
    );
    let tags = vec![tag(0)];
    let run = |sibling_tags: &[String]| {
        let mut catchall = test_vc(700);
        catchall.kind = VcKind::Assertion { message: "panic freedom: grounded".into() };
        catchall.formula = contradiction.clone();
        let results = vec![(catchall, authority_test_proved()), row(701, sibling_tags)];
        let disclosure = TinvRowDisclosure::from_parts(
            Some(published(&[0])),
            if sibling_tags.is_empty() {
                vec![]
            } else {
                vec![record(&results[1].0, sibling_tags)]
            },
        );
        let receipts = receipts(&results);
        // Only the catch-all is kernel-certified: the sibling is graded by S1 (Trusted).
        let mut certificates = certify_all(&results, None);
        certificates[1] = None;
        let mut authorities = build_result_proof_authorities_with_revalidations(
            &results,
            &[],
            None,
            &certificates,
            &receipts,
        );
        mint_type_invariant_composed_authorities(
            &results,
            &[],
            &receipts,
            &mut authorities,
            &disclosure,
        );
        cap_type_invariant_authorities(&results, &mut authorities, &disclosure);
        assert!(matches!(authorities[0], Some(ResultProofAuthority::KernelCertified { .. })));
        let identity = |index: usize| exact_result_row_identity(index, &results[index].0);
        let grounding = GroundedCatchallPremises {
            row: identity(0).unwrap(),
            premises: vec![(1, identity(1))],
            calls: GroundedCallPremise::Absent,
        };
        cap_grounded_panic_freedom_authorities(
            &results,
            &[],
            &mut authorities,
            None,
            std::slice::from_ref(&grounding),
        );
        authorities
    };
    let control = run(&[]);
    assert!(
        matches!(control[0], Some(ResultProofAuthority::GroundedPanicFreedomDerivation { .. })),
        "control: an S1 sibling grades the catch-all Trusted: {:?}",
        control[0]
    );
    let premised = run(&tags);
    assert!(matches!(premised[1], Some(ResultProofAuthority::TypeInvariantComposed { .. })));
    assert!(premised[0].is_none(), "the catch-all kept a token over a TINV premise");
}

/// Review fold-in 3: ONE E9 policy on both lanes. The in-walk lane installs before the
/// cap, which strips an E9 authority from every row of a premised body; the post-walk
/// lane installs after it and asks `tinv_refuses_post_cap_authority`, which refuses the
/// same rows (and any tagged row).
#[test]
fn e9_authorities_follow_one_tinv_policy_on_both_lanes() {
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags), row(2, &[])];
    let e9 = |index: usize| ResultProofAuthority::EnsuresCitationDischarge {
        row: exact_result_row_identity(index, &results[index].0).unwrap(),
        theorem: "thm".into(),
        evidence: Some(super::authority_test_clean_cic(0x70 + index as u8)),
        reference: super::authority_test_reference(&super::authority_test_clean_cic(
            0x70 + index as u8,
        )),
    };
    // In-walk: installed, then capped in a premised body.
    let premised =
        TinvRowDisclosure::from_parts(Some(published(&[0])), vec![record(&results[0].0, &tags)]);
    let mut authorities = vec![Some(e9(0)), Some(e9(1))];
    assert_eq!(cap_type_invariant_authorities(&results, &mut authorities, &premised), 2);
    assert!(authorities.iter().all(Option::is_none));
    // Post-walk: the same rows are refused.
    assert!(tinv_refuses_post_cap_authority(true, &results[0].0, &e9(0)));
    assert!(tinv_refuses_post_cap_authority(true, &results[1].0, &e9(1)));
    // A tagged row is refused even outside a recorded body.
    assert!(tinv_refuses_post_cap_authority(false, &results[0].0, &e9(0)));
    // Control: an untagged row of a body with no premise keeps its E9 on both lanes.
    assert!(!tinv_refuses_post_cap_authority(false, &results[1].0, &e9(1)));
    let mut clear = vec![None, Some(e9(1))];
    assert_eq!(
        cap_type_invariant_authorities(&results, &mut clear, &TinvRowDisclosure::default()),
        0
    );
}

/// Review fold-in 4: the tags are decoded against the set the GENERATION used, and only
/// when it is exactly the stored, published set; two sets in one generation, a different
/// set, or no stored set refuse every tagged row.
#[test]
fn the_disclosure_decodes_only_against_the_generations_own_published_set() {
    use trust_vcgen::type_invariant::TinvGenerationRecord;
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags)];
    // No real use set can be built here (certificates come from Houdini alone), so the
    // identity rule is exercised through `from_record` with `None`/conflict shapes, and the
    // decode itself through `from_parts`.
    let record = TinvGenerationRecord {
        rows: vec![record(&results[0].0, &tags)],
        use_set: None,
        conflicting_sets: false,
    };
    let none = TinvRowDisclosure::from_record(None, &record, &BTreeMap::new());
    assert!(matches!(none.row_status(&results[0].0), TinvRowStatus::Refused(_)));
    assert!(none.body_carries_premise(), "the record still marks the body premised");
    let conflicting = TinvGenerationRecord { conflicting_sets: true, ..record };
    let refused = TinvRowDisclosure::from_record(None, &conflicting, &BTreeMap::new());
    assert!(matches!(refused.row_status(&results[0].0), TinvRowStatus::Refused(_)));
}

/// TINV-28 amended (step 10.7): a minted `TypeInvariantComposed` row reads `Trusted`
/// (never `Certified`) WITH its premise on every compiler surface — the proof results'
/// `premises`, the telemetry's `assumes`, the transport row's `assumes` — and the strict L0
/// count credits it exactly as it credits the other disclosed `Trusted` grades. The
/// untagged sibling is unchanged and carries no premise anywhere.
#[test]
fn a_composed_row_reads_trusted_with_its_premise_on_every_surface() {
    // `Symbol::intern` (the premises' spelling) needs session globals.
    rustc_span::create_default_session_globals_then(|| {
        let tags = vec![tag(0)];
        let results = vec![row(1, &tags), row(2, &[])];
        let disclosure = TinvRowDisclosure::from_parts(
            Some(published(&[0])),
            vec![record(&results[0].0, &tags)],
        );
        let authorities = mint(&results, &disclosure);
        assert!(matches!(authorities[0], Some(ResultProofAuthority::TypeInvariantComposed { .. })));
        let label = trust_types::type_invariant_assumes_label(TY, 0);
        for overflow_checks in [true, false] {
            let proof_results = build_proof_results_with_runtime_checks(
                overflow_checks,
                &results,
                &[],
                &[],
                &authorities,
                None,
            );
            let composed = proof_results.dispositions.iter().next().expect("row 0");
            assert_eq!(composed.status, TrustStatus::Trusted);
            assert_eq!(composed.strength, TrustProofStrength::Deductive);
            assert!(!composed.certified);
            let (vc, result) = &results[0];
            assert_eq!(
                convert_result(overflow_checks, 0, vc, None, result, authorities[0].as_ref()),
                (TrustStatus::Trusted, TrustProofStrength::Deductive),
            );
            assert_eq!(proof_results.summary.trusted, 2, "{:?}", proof_results.summary);
            assert_eq!(proof_results.summary.certified, 0);
            assert_eq!(proof_results.premises.len(), 1, "{:?}", proof_results.premises);
            assert_eq!(
                proof_results.premises_of(ObligationId::from_usize(0)),
                &[Symbol::intern(&label)][..]
            );
            assert!(proof_results.premises_of(ObligationId::from_usize(1)).is_empty());
            assert!(proof_results.has_aligned_obligation_arrays());
        }
        // A premise on a Certified disposition is rejected by the alignment check.
        let mut forged =
            build_proof_results_with_runtime_checks(true, &results, &[], &[], &authorities, None);
        forged.dispositions[ObligationId::from_usize(0)].status = TrustStatus::Certified;
        assert!(!forged.has_aligned_obligation_arrays(), "a premised row read Certified");
        // Telemetry and transport carry the same line, and only on the composed row.
        let telemetry = build_proof_telemetry_with(&|_| true, &results, &[], &authorities);
        assert_eq!(
            telemetry.details[ObligationId::from_usize(0)].assumes,
            vec![Symbol::intern(&label)]
        );
        assert!(telemetry.details[ObligationId::from_usize(1)].assumes.is_empty());
        assert!(telemetry.details[ObligationId::from_usize(0)].runtime_fallback.is_none());
        let transport = build_transport_results_with_runtime_checks_bound(
            true,
            None,
            &results,
            None,
            &[],
            &[],
            &authorities,
        );
        assert_eq!(transport[0].assumes, vec![label.clone()]);
        assert_eq!(transport[0].outcome, trust_types::Outcome::Proved);
        assert!(transport[0].proof_evidence.is_none(), "no public evidence envelope");
        assert!(transport[1].assumes.is_empty());
        // The strict L0 count credits it like every other disclosed Trusted grade.
        let failure = strict_l0_verification_failure(
            true,
            &results,
            &[],
            &authorities,
            None,
            &OpenDispatchRefutationWitnesses::default(),
        );
        assert!(failure.is_none(), "{failure:?}");
    });
}

/// Step 10.7: a token whose disclosure does not render exactly its premises does not
/// bind its row (so it reads nothing, on any surface), and a disclosure without a
/// rendering for a premise mints nothing.
#[test]
fn a_composed_token_binds_only_with_a_matching_disclosure() {
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags)];
    let disclosure =
        TinvRowDisclosure::from_parts(Some(published(&[0])), vec![record(&results[0].0, &tags)]);
    let authorities = mint(&results, &disclosure);
    let Some(ResultProofAuthority::TypeInvariantComposed { row, receipt, assumes, .. }) =
        authorities[0].clone()
    else {
        panic!("{:?}", authorities[0]);
    };
    let (vc, result) = &results[0];
    for bad in [
        vec![],
        vec!["assumes nothing".to_string()],
        vec![trust_types::type_invariant_assumes_label(TY, 1)],
        vec![format!("{}x", trust_types::type_invariant_assumes_label(TY, 0))],
        vec![trust_types::type_invariant_assumes_label(TY, 0); 2],
    ] {
        let forged = ResultProofAuthority::TypeInvariantComposed {
            row: row.clone(),
            receipt: receipt.clone(),
            assumes: assumes.clone(),
            disclosure: bad.clone(),
        };
        assert!(!forged.matches_row(0, vc, None), "{bad:?}");
        assert!(!forged.is_static_proof_for(0, vc, result, None), "{bad:?}");
        assert!(forged.type_invariant_disclosure_for(0, vc, result, None).is_none());
    }
    // No rendering for the premise: nothing is minted (the row reads unproved).
    let unrendered = TinvRowDisclosure::from_record(
        None,
        &trust_vcgen::type_invariant::TinvGenerationRecord::default(),
        &BTreeMap::new(),
    );
    assert!(unrendered.render(&assumes).is_none());
}

/// Step 10.5 LIVENESS (KNOWN_HAZARDS 10.5 (a)): the install is `Arc::clone` of the stored
/// published set, and only that is live. A REBUILT or DEEP-CLONED set (equal content,
/// another allocation) is detected — `installed_use_set_is_live` is false, so the install
/// point withdraws it — and a generation whose facts came from such a set has every tagged
/// row refused with a reason that names the mismatch, never silently graded. The flag off
/// installs nothing.
#[test]
fn installing_a_rebuilt_or_deep_cloned_use_set_is_detected_and_refused() {
    use std::sync::Arc;

    use trust_vcgen::type_invariant::houdini::TinvOutcome;
    use trust_vcgen::type_invariant::{TinvGenerationRecord, TinvUseSet};

    use super::super::type_invariant::{installable_use_set, installed_use_set_is_live};

    let outcome = TinvOutcome::<()>::default();
    let stored = Arc::new(TinvUseSet::from_outcome(&outcome, |_| true).expect("use set"));
    // The flag gates the install; on, it is the SAME allocation.
    assert!(installable_use_set(false, Some(&stored)).is_none());
    let installed = installable_use_set(true, Some(&stored)).expect("installed");
    assert!(Arc::ptr_eq(&installed, &stored));
    assert!(installed_use_set_is_live(Some(&installed), Some(&stored)));
    assert!(installed_use_set_is_live::<TinvUseSet>(None, Some(&stored)), "nothing installed");
    // A deep clone and a rebuild: equal content, another allocation — NOT live.
    let deep = Arc::new((*stored).clone());
    let rebuilt = Arc::new(TinvUseSet::from_outcome(&outcome, |_| true).expect("use set"));
    assert_eq!(*deep, *stored);
    for copy in [&deep, &rebuilt] {
        assert!(!installed_use_set_is_live(Some(copy), Some(&stored)));
    }
    assert!(!installed_use_set_is_live(Some(&installed), None), "installed with none stored");
    // A generation that drew its facts from the copy: every tagged row refused, by name.
    let tags = vec![tag(0)];
    let results = vec![row(1, &tags)];
    let rendered: BTreeMap<(String, u32), String> =
        [((TY.to_string(), 0), trust_types::type_invariant_assumes_label(TY, 0))].into();
    for copy in [&deep, &rebuilt] {
        let record = TinvGenerationRecord {
            rows: vec![record(&results[0].0, &tags)],
            use_set: Some(Arc::clone(copy)),
            conflicting_sets: false,
        };
        let disclosure = TinvRowDisclosure::from_record(Some(&stored), &record, &rendered);
        match disclosure.row_status(&results[0].0) {
            TinvRowStatus::Refused(why) => {
                assert!(why.contains("not the session's stored published set"), "{why}")
            }
            other => panic!("a copied set was accepted: {other:?}"),
        }
        assert!(mint(&results, &disclosure)[0].is_none());
    }
}
