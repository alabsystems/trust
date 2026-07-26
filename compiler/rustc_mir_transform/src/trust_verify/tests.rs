// ignore-tidy-filelength
#![allow(rustc::symbol_intern_string_literal)]

use rustc_index::IndexVec;
use rustc_middle::mir::trust_proof::{
    TrustDisposition, TrustFunctionSummary, TrustObligationDetail, TrustObligationKind,
    TrustProofLevel, TrustProofResults, TrustProofStrength, TrustRuntimeFallbackReason,
    TrustStatus,
};
use rustc_session::TrustCrateRole;
use trust_router::full_verification::{
    FullVerificationEvidenceBlocker, FullVerificationRunResultExt,
};

use super::*;

/// These carrier fixtures have no compiler `Session`, and therefore no
/// session-owned panic-freedom grounding inventory. Keep that absence explicit
/// while exercising the same validation core as production.
fn native_proved_authority_validation_failures(
    result: Option<&trust_verifier_api::VerificationRunResult>,
    results: &[(VerificationCondition, VerificationResult)],
    result_bindings: &[Option<ResultObligationBinding>],
    proof_authorities: &[Option<ResultProofAuthority>],
) -> Vec<String> {
    native_proved_authority_validation_failures_with_grounding_lookup(
        result,
        results,
        result_bindings,
        proof_authorities,
        |_| None,
    )
}

#[test]
fn r1_synthetic_substitution_resolves_exact_acyclic_chain() {
    let substitutions = vec![
        (
            "_3".to_string(),
            Formula::Add(
                Box::new(Formula::Var("_4".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            ),
        ),
        ("_4".to_string(), Formula::Var("x".to_string(), Sort::Int)),
    ];
    let input =
        Formula::Eq(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Int(2)));
    let expected = Formula::Eq(
        Box::new(Formula::Add(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(1)),
        )),
        Box::new(Formula::Int(2)),
    );

    assert_eq!(resolve_r1_synthetic_substitutions(&input, &substitutions), Some(expected));
}

#[test]
fn r1_synthetic_substitution_consumers_preserve_valid_formula_parity() {
    let int_var = |name: &str| Formula::Var(name.to_string(), Sort::Int);
    let violation = Formula::And(vec![
        Formula::Eq(Box::new(int_var("_3")), Box::new(int_var("i"))),
        Formula::Lt(Box::new(int_var("_3")), Box::new(int_var("n"))),
        Formula::Ge(Box::new(int_var("_3")), Box::new(int_var("arr__slice_len"))),
    ]);

    assert_eq!(
        simplify_violation_negation(&violation),
        Some(Formula::Or(vec![
            Formula::Ge(Box::new(int_var("i")), Box::new(int_var("n"))),
            Formula::Lt(Box::new(int_var("i")), Box::new(int_var("arr__slice_len")),),
        ])),
    );
    assert_eq!(
        synthesize_loop_bound_precondition(&violation),
        Some(Formula::Le(Box::new(int_var("n")), Box::new(int_var("arr__slice_len")),)),
    );
}

#[test]
fn r1_synthetic_substitution_cycle_fails_closed_in_both_consumers() {
    let mut conjuncts = vec![
        Formula::Eq(
            Box::new(Formula::Var("_3".to_string(), Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::Var("_4".to_string(), Sort::Int)),
                Box::new(Formula::Var("_4".to_string(), Sort::Int)),
            )),
        ),
        Formula::Eq(
            Box::new(Formula::Var("_4".to_string(), Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::Var("_3".to_string(), Sort::Int)),
                Box::new(Formula::Var("_3".to_string(), Sort::Int)),
            )),
        ),
        Formula::Lt(
            Box::new(Formula::Var("_3".to_string(), Sort::Int)),
            Box::new(Formula::Var("n".to_string(), Sort::Int)),
        ),
        Formula::Ge(
            Box::new(Formula::Var("_3".to_string(), Sort::Int)),
            Box::new(Formula::Var("arr__slice_len".to_string(), Sort::Int)),
        ),
    ];
    // The former fixed-point loop used the total binding count as its round
    // count, so irrelevant bindings made the two-node cycle expand until OOM.
    for index in 0..128 {
        conjuncts.push(Formula::Eq(
            Box::new(Formula::Var(format!("_irrelevant_{index}"), Sort::Int)),
            Box::new(Formula::Int(index)),
        ));
    }
    let violation = Formula::And(conjuncts);

    assert_eq!(simplify_violation_negation(&violation), None);
    assert_eq!(synthesize_loop_bound_precondition(&violation), None);
}

#[test]
fn r1_synthetic_substitution_direct_cycle_and_irrelevant_cycle_are_distinct() {
    let self_cycle = vec![("_0".to_string(), Formula::Var("_0".to_string(), Sort::Int))];
    assert_eq!(
        resolve_r1_synthetic_substitutions(&Formula::Var("_0".to_string(), Sort::Int), &self_cycle,),
        None,
    );

    assert_eq!(
        resolve_r1_synthetic_substitutions(&Formula::Var("x".to_string(), Sort::Int), &self_cycle,),
        Some(Formula::Var("x".to_string(), Sort::Int)),
        "an unreachable cycle must not poison an unrelated core formula",
    );
}

#[test]
fn r1_synthetic_substitution_duplicate_binding_keeps_first() {
    let substitutions =
        vec![("_0".to_string(), Formula::Int(1)), ("_0".to_string(), Formula::Int(2))];
    assert_eq!(
        resolve_r1_synthetic_substitutions(
            &Formula::Var("_0".to_string(), Sort::Int),
            &substitutions,
        ),
        Some(Formula::Int(1)),
    );
}

#[test]
fn r1_synthetic_substitution_depth_boundary_is_exact() {
    fn chain(last: usize) -> Vec<(String, Formula)> {
        let mut substitutions = (0..last)
            .map(|index| (format!("_{index}"), Formula::Var(format!("_{}", index + 1), Sort::Int)))
            .collect::<Vec<_>>();
        substitutions.push((format!("_{last}"), Formula::Var("x".to_string(), Sort::Int)));
        substitutions
    }

    let input = Formula::Var("_0".to_string(), Sort::Int);
    assert_eq!(
        resolve_r1_synthetic_substitutions(&input, &chain(R1_SUBSTITUTION_DEPTH_BUDGET - 1),),
        Some(Formula::Var("x".to_string(), Sort::Int)),
    );
    assert_eq!(
        resolve_r1_synthetic_substitutions(&input, &chain(R1_SUBSTITUTION_DEPTH_BUDGET)),
        None,
    );
}

#[test]
fn r1_synthetic_substitution_batch_shares_one_budget() {
    let first = Formula::Bool(true);
    let second = Formula::Bool(false);
    let formulas = [&first, &second];
    let mut exact = R1SubstitutionBudget::with_work(4);
    assert_eq!(
        resolve_r1_synthetic_substitution_batch(&formulas, &[], &mut exact),
        Some(vec![first.clone(), second.clone()]),
    );

    let mut one_short = R1SubstitutionBudget::with_work(3);
    assert_eq!(
        resolve_r1_synthetic_substitution_batch(&formulas, &[], &mut one_short),
        None,
        "preflight and output reconstruction must share one batch budget",
    );
}

#[test]
fn r1_synthetic_substitution_honors_and_restores_ambient_deadline() {
    let input = Formula::Bool(true);
    let formulas = [&input];

    {
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(
            Some(std::time::Instant::now()),
            0,
        );
        assert_eq!(
            resolve_r1_synthetic_substitution_batch(
                &formulas,
                &[],
                &mut R1SubstitutionBudget::new(),
            ),
            None,
            "expired preprocessing must fail closed before cloning the candidate",
        );
    }

    assert_eq!(
        resolve_r1_synthetic_substitution_batch(&formulas, &[], &mut R1SubstitutionBudget::new(),),
        Some(vec![input.clone()]),
        "the RAII deadline scope must restore the prior ambient budget",
    );
}

#[test]
fn r1_synthetic_substitution_rejects_oversized_input_before_clone() {
    let oversized = Formula::And(vec![Formula::Bool(true); R1_SUBSTITUTION_WORK_BUDGET]);
    assert_eq!(resolve_r1_synthetic_substitutions(&oversized, &[]), None);
}

#[test]
fn r1_synthetic_substitution_exponential_acyclic_chain_hits_node_budget() {
    let mut substitutions = Vec::new();
    for index in 0..32 {
        let next = Formula::Var(format!("_{}", index + 1), Sort::Int);
        substitutions
            .push((format!("_{index}"), Formula::Add(Box::new(next.clone()), Box::new(next))));
    }
    substitutions.push(("_32".to_string(), Formula::Var("x".to_string(), Sort::Int)));

    assert_eq!(
        resolve_r1_synthetic_substitutions(
            &Formula::Var("_0".to_string(), Sort::Int),
            &substitutions,
        ),
        None,
        "an acyclic substitution whose materialized tree is exponential must fail closed"
    );
}

#[test]
fn r1_synthetic_substitution_rejects_deep_or_oversized_metadata_before_clone() {
    let mut deep_sort = Sort::Int;
    for _ in 0..=R1_SUBSTITUTION_DEPTH_BUDGET {
        deep_sort = Sort::Array(Box::new(deep_sort), Box::new(Sort::Int));
    }
    assert_eq!(
        resolve_r1_synthetic_substitutions(&Formula::Var("x".to_string(), deep_sort), &[],),
        None,
        "Sort recursion is part of the derive-Clone depth bound",
    );

    assert_eq!(
        resolve_r1_synthetic_substitutions(
            &Formula::Var("x".repeat(R1_SUBSTITUTION_WORK_BUDGET), Sort::Int),
            &[],
        ),
        None,
        "retained metadata bytes share the structural work budget",
    );
}

#[test]
fn r1_synthetic_substitution_charges_metadata_for_every_materialized_occurrence() {
    let replacement = Formula::Var("x".repeat(20_000), Sort::Int);
    let input = Formula::And(vec![Formula::Var("_0".to_string(), Sort::Int); 4]);
    assert_eq!(
        resolve_r1_synthetic_substitutions(&input, &[("_0".to_string(), replacement)]),
        None,
        "one preflight must not license unbounded repeated metadata clones",
    );
}

#[test]
fn r1_candidate_collection_charges_lhs_and_type_range_names_before_scans() {
    let giant_synthetic = Formula::Var(format!("{}#", "x".repeat(1_000)), Sort::Int);
    let substitution = Formula::Eq(Box::new(giant_synthetic), Box::new(Formula::Int(0)));
    let violation = Formula::And(vec![substitution, Formula::Bool(true)]);
    assert!(
        collect_r1_candidate_parts(&violation, &mut R1SubstitutionBudget::with_work(128)).is_none(),
        "substitution-LHS classification must charge the retained name bytes",
    );

    let giant_key = format!("{}#", "k".repeat(1_000));
    let input = Formula::Bool(true);
    let replacement = Formula::Bool(false);
    assert_eq!(
        resolve_r1_synthetic_substitution_batch(
            &[&input],
            &[(giant_key.as_str(), &replacement)],
            &mut R1SubstitutionBudget::with_work(128),
        ),
        None,
        "helper-supplied substitution keys must be charged before hash-map insertion",
    );

    let giant_name = "range_name".repeat(100);
    let var = || Formula::Var(giant_name.clone(), Sort::Int);
    let type_range = Formula::And(vec![
        Formula::Ge(Box::new(var()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(var()), Box::new(Formula::Int(255))),
    ]);
    assert!(
        collect_r1_candidate_parts(&type_range, &mut R1SubstitutionBudget::with_work(128))
            .is_none(),
        "the two-bound fast path must charge names before comparing them",
    );
}

#[test]
fn r1_loop_bound_pair_scan_shares_the_candidate_work_budget() {
    let int_var = |name: &str| Formula::Var(name.to_string(), Sort::Int);
    let mut conjuncts = (0..8)
        .map(|index| {
            Formula::Ge(Box::new(int_var(&format!("i{index}"))), Box::new(int_var("a__slice_len")))
        })
        .collect::<Vec<_>>();
    conjuncts.push(Formula::Lt(Box::new(int_var("i7")), Box::new(int_var("n"))));
    let violation = Formula::And(conjuncts);
    let expected = Formula::Le(Box::new(int_var("n")), Box::new(int_var("a__slice_len")));

    assert_eq!(
        synthesize_loop_bound_precondition_with_budget(
            &violation,
            R1SubstitutionBudget::with_work(1_000),
        ),
        Some(expected),
    );
    assert_eq!(
        synthesize_loop_bound_precondition_with_budget(
            &violation,
            R1SubstitutionBudget::with_work(420),
        ),
        None,
        "the quadratic match phase must stop when the shared budget is exhausted",
    );
}

#[test]
fn exact_liskov_identity_is_structural_and_mutations_fail_closed() {
    let trait_contract = trust_vcgen::TraitContract {
        trait_name: "demo::Widget".to_string(),
        method: "rank".to_string(),
        parameter_names: vec!["self".to_string(), "x".to_string(), "y".to_string()],
        preconditions: Vec::new(),
        postconditions: vec![Formula::Ge(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )],
    };
    let exact_impl = trust_vcgen::ImplContract {
        impl_type: "demo::Button".to_string(),
        method: "rank".to_string(),
        parameter_names: trait_contract.parameter_names.clone(),
        preconditions: Vec::new(),
        postconditions: trait_contract.postconditions.clone(),
    };
    assert!(trust_vcgen::liskov_contracts_have_exact_identity(&trait_contract, &exact_impl,));

    let mut changed_postcondition = exact_impl.clone();
    changed_postcondition.postconditions = vec![Formula::Bool(false)];
    assert!(!trust_vcgen::liskov_contracts_have_exact_identity(
        &trait_contract,
        &changed_postcondition,
    ));

    let mut changed_precondition = exact_impl.clone();
    changed_precondition.preconditions = vec![Formula::Bool(true)];
    assert!(!trust_vcgen::liskov_contracts_have_exact_identity(
        &trait_contract,
        &changed_precondition,
    ));

    let mut swapped_binders = exact_impl.clone();
    swapped_binders.parameter_names = vec!["self".to_string(), "y".to_string(), "x".to_string()];
    assert!(
        !trust_vcgen::liskov_contracts_have_exact_identity(&trait_contract, &swapped_binders),
        "the same formula spelling denotes a different argument after binder reordering"
    );
    let mismatch_vcs = trust_vcgen::verify_liskov(&trait_contract, &swapped_binders);
    assert_eq!(mismatch_vcs.len(), 1);
    assert_eq!(mismatch_vcs[0].formula, Formula::Bool(true));
}

#[test]
fn dyn_summary_in_progress_guard_restores_after_unwind() {
    let def_id = rustc_span::def_id::CRATE_DEF_ID.to_def_id();
    DYN_SUMMARY_IN_PROGRESS.with(|in_progress| {
        assert!(!in_progress.borrow().contains(&def_id));
    });

    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = DynSummaryInProgressGuard::enter(def_id).expect("first frame owns entry");
        DYN_SUMMARY_IN_PROGRESS.with(|in_progress| {
            assert!(in_progress.borrow().contains(&def_id));
        });
        assert!(
            DynSummaryInProgressGuard::enter(def_id).is_none(),
            "a nested frame must not remove the outer frame's entry"
        );
        panic!("exercise unwind cleanup");
    }));
    assert!(unwind.is_err());

    DYN_SUMMARY_IN_PROGRESS.with(|in_progress| {
        assert!(!in_progress.borrow().contains(&def_id));
    });
    let guard = DynSummaryInProgressGuard::enter(def_id)
        .expect("a later verification frame must be able to re-enter");
    drop(guard);
    DYN_SUMMARY_IN_PROGRESS.with(|in_progress| {
        assert!(!in_progress.borrow().contains(&def_id));
    });
}

fn private_proof_store_test_root(label: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};

    static SEQUENCE: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "trustc-proof-store-{label}-{}-{}",
        std::process::id(),
        SEQUENCE.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).expect("create proof store test root");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))
            .expect("make proof store test root private");
    }
    path.canonicalize().expect("canonical proof store test root")
}

#[test]
fn proof_artifact_store_requires_owner_private_root_and_components() {
    let root = private_proof_store_test_root("private");
    let (_canonical_root, store) =
        prepare_private_proof_artifact_store(&root).expect("private store should be accepted");
    assert_eq!(store.file_name(), Some(std::ffi::OsStr::new("sha256")));
    assert_eq!(
        store.parent().and_then(Path::file_name),
        Some(std::ffi::OsStr::new(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY))
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        assert_eq!(
            std::fs::metadata(&store).expect("store metadata").permissions().mode() & 0o777,
            0o700
        );
        assert_eq!(
            std::fs::metadata(store.parent().expect("store parent"))
                .expect("store parent metadata")
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
    }
    std::fs::remove_dir_all(root).expect("remove proof store test root");
}

#[cfg(unix)]
#[test]
fn proof_artifact_store_rejects_non_private_root() {
    use std::os::unix::fs::PermissionsExt as _;

    let root = private_proof_store_test_root("public");
    std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o755))
        .expect("make root public");
    let error = prepare_private_proof_artifact_store(&root)
        .expect_err("world-readable proof root must fail closed");
    assert!(error.contains("mode 0700"), "unexpected error: {error}");
    std::fs::remove_dir_all(root).expect("remove proof store test root");
}

#[cfg(unix)]
#[test]
fn proof_artifact_store_rejects_symlinked_fixed_components() {
    use std::os::unix::fs::{PermissionsExt as _, symlink};

    for symlink_sha256 in [false, true] {
        let root =
            private_proof_store_test_root(if symlink_sha256 { "sha-link" } else { "store-link" });
        let outside = private_proof_store_test_root(if symlink_sha256 {
            "sha-outside"
        } else {
            "store-outside"
        });
        let store_root = root.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        if symlink_sha256 {
            std::fs::create_dir(&store_root).expect("create real store component");
            std::fs::set_permissions(&store_root, std::fs::Permissions::from_mode(0o700))
                .expect("make real store component private");
            symlink(&outside, store_root.join("sha256")).expect("symlink sha256 component");
        } else {
            symlink(&outside, &store_root).expect("symlink store component");
        }

        let error = prepare_private_proof_artifact_store(&root)
            .expect_err("symlinked proof store component must fail closed");
        assert!(
            error.contains("non-symlink") || error.contains("symlink"),
            "unexpected error: {error}"
        );
        assert!(
            std::fs::read_dir(&outside).expect("read outside directory").next().is_none(),
            "rejected proof store traversal must not materialize outside its authority root"
        );
        std::fs::remove_dir_all(root).expect("remove proof store test root");
        std::fs::remove_dir_all(outside).expect("remove outside proof store root");
    }
}

/// `survey` names the historical boolean these tests were written against.
/// `TrustVerifyPolicy` now carries the selected `-Ztrust-policy` instead, and
/// `survey` was exactly "advisory rather than strict", so it maps onto that.
fn test_policy(survey: bool, include_dependencies: bool) -> TrustVerifyPolicy {
    TrustVerifyPolicy {
        include_dependencies,
        policy: if survey {
            rustc_session::config::TrustPolicy::Advisory
        } else {
            rustc_session::config::TrustPolicy::Strict
        },
    }
}

fn test_vc(line_start: u32) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: trust_types::Symbol::intern("test::f"),
        location: trust_types::SourceSpan {
            file: "test.rs".to_string(),
            line_start,
            col_start: 1,
            line_end: line_start,
            col_end: 5,
        },
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
    }
}

#[test]
fn forced_allocation_after_backend_decline_is_an_explicit_structural_refutation() {
    // Trust: an interval decline on this structurally forced allocation must
    // become an ordinary Failed result, never reach the unwitnessed-Proved ICE.
    let int_var = |name: &str| Formula::Var(name.to_string(), Sort::Int);
    let a = int_var("a");
    let sum = Formula::Add(Box::new(a.clone()), Box::new(Formula::Int(1)));
    let count = int_var("count");
    let ceiling = Formula::Int(1 << 28);
    let mut vc = test_vc(8);
    vc.kind = VcKind::UnboundedAllocation {
        callee: "vec![value; count]".into(),
        count: "count".into(),
        detail: "forced allocation beside safe arithmetic sibling".to_string(),
    };
    vc.formula = Formula::And(vec![
        Formula::Ge(Box::new(a.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(a), Box::new(Formula::Int(255))),
        Formula::Or(vec![
            Formula::Gt(Box::new(sum.clone()), Box::new(Formula::Int(i128::from(u32::MAX)))),
            Formula::Eq(Box::new(int_var("sum")), Box::new(sum)),
        ]),
        Formula::Eq(Box::new(count.clone()), Box::new(ceiling.clone())),
        Formula::Le(Box::new(count.clone()), Box::new(ceiling.clone())),
        Formula::Ge(Box::new(count), Box::new(ceiling)),
    ]);

    let mut results = vec![(
        vc,
        VerificationResult::Unknown {
            solver: "interval".into(),
            time_ms: 0,
            reason: "direct forced allocation cannot be discharged".to_string(),
        },
    )];
    refute_forced_unbounded_allocations(&mut results);

    let VerificationResult::Failed { solver, counterexample, .. } = &results[0].1 else {
        panic!("forced allocation must become an explicit failed verdict");
    };
    assert_eq!(solver.as_str(), "structural-forced-unbounded-allocation");
    assert!(counterexample.is_none());
}

#[test]
fn overflow_check_origins_preserve_repeated_rows_from_one_block() {
    let vc = test_vc(7);
    let canonical_vc =
        canonical_exact_vc_payload(&vc).expect("test VC must have a canonical payload");
    let origins = OverflowCheckOrigins::from_pairs(&[
        (trust_types::BlockId(3), vc.clone()),
        (trust_types::BlockId(3), vc),
    ]);

    assert_eq!(
        origins.resolve(&canonical_vc),
        Some(BasicBlock::from_usize(3)),
        "dedupe or repeated emission from one MIR block must retain its unique origin"
    );
}

#[test]
fn overflow_check_origins_fail_closed_for_identical_vcs_from_distinct_blocks() {
    let vc = test_vc(8);
    let canonical_vc =
        canonical_exact_vc_payload(&vc).expect("test VC must have a canonical payload");
    let origins = OverflowCheckOrigins::from_pairs(&[
        (trust_types::BlockId(4), vc.clone()),
        (trust_types::BlockId(9), vc),
    ]);

    assert_eq!(
        origins.resolve(&canonical_vc),
        None,
        "one exact VC shared by distinct MIR blocks must be ambiguous and ineligible for elision"
    );
    assert_eq!(origins.0.get(&canonical_vc), Some(&OverflowOrigin::Ambiguous));
}

#[test]
fn overflow_check_origins_key_by_exact_vc_not_source_span() {
    let true_vc = test_vc(9);
    let mut false_vc = true_vc.clone();
    false_vc.formula = Formula::Bool(false);
    let true_key =
        canonical_exact_vc_payload(&true_vc).expect("true test VC must have a canonical payload");
    let false_key =
        canonical_exact_vc_payload(&false_vc).expect("false test VC must have a canonical payload");
    assert_ne!(true_key, false_key, "the formula must participate in the origin identity");

    let origins = OverflowCheckOrigins::from_pairs(&[
        (trust_types::BlockId(5), true_vc),
        (trust_types::BlockId(6), false_vc),
    ]);

    assert_eq!(origins.resolve(&true_key), Some(BasicBlock::from_usize(5)));
    assert_eq!(origins.resolve(&false_key), Some(BasicBlock::from_usize(6)));
    assert_eq!(
        origins.resolve("not a canonical verification condition"),
        None,
        "an absent exact identity must never inherit authority from a nearby source span"
    );
}

#[test]
fn exact_vc_claim_digest_binds_every_claim_dimension() {
    let base = test_vc(10);
    let canonical_payload =
        canonical_exact_vc_claim_payload(&base, false, None).expect("test VC claim must serialize");
    let base_digest =
        exact_vc_claim_digest_sha256(&base, false, None).expect("test VC must have a claim digest");
    assert_eq!(base_digest.len(), 64);
    let expected_digest =
        domain_length_bound_sha256_hex(EXACT_VC_CLAIM_DIGEST_DOMAIN, canonical_payload.as_bytes());
    assert_eq!(
        base_digest, expected_digest,
        "transport claim digest must use the exact canonical VC payload and protocol domain"
    );
    let payload: serde_json::Value =
        serde_json::from_str(&canonical_payload).expect("canonical claim payload must be JSON");
    assert_eq!(payload["schema"], EXACT_VC_CLAIM_SCHEMA_VERSION);
    assert_eq!(payload["semantics"]["overflow_checks"], false);
    assert!(payload["semantics"]["target"].is_null());
    assert!(payload.get("vc").is_some(), "schema wrapper must retain the complete VC");
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("mock"),
        time_ms: 1,
        reason: "claim binding probe".to_string(),
    };
    let rows = build_transport_results_with_runtime_checks(
        false,
        &[(base.clone(), unknown)],
        None,
        Some(&[None]),
    );
    assert_eq!(
        rows[0].claim_digest_sha256.as_deref(),
        Some(base_digest.as_str()),
        "every real VC transport row must carry the exact claim digest"
    );
    assert_eq!(
        rows[0].typed_kind.as_deref(),
        Some(&base.kind),
        "every real VC transport row must carry the producer's exact typed kind"
    );
    assert_eq!(rows[0].kind, base.kind.transport_tag());
    assert_eq!(rows[0].description, base.kind.description());

    let assert_changed = |dimension: &str, changed: VerificationCondition| {
        assert_ne!(
            exact_vc_claim_digest_sha256(&changed, false, None).as_deref(),
            Some(base_digest.as_str()),
            "changing the VC {dimension} must change its transport claim digest"
        );
    };

    let mut changed = base.clone();
    changed.formula = trust_types::Formula::Bool(false);
    assert_changed("formula", changed);

    let mut changed = base.clone();
    changed.function = trust_types::Symbol::intern("test::different_function");
    assert_changed("function", changed);

    let mut changed = base.clone();
    changed.location.file = "different-source.rs".to_string();
    assert_changed("source", changed);

    let mut changed = base.clone();
    changed.kind = VcKind::RemainderByZero;
    assert_changed("kind", changed);

    let mut changed = base;
    changed.contract_metadata = Some(trust_types::ContractMetadata {
        has_requires: true,
        ..trust_types::ContractMetadata::default()
    });
    assert_changed("contract metadata", changed);

    assert_ne!(
        exact_vc_claim_digest_sha256(&test_vc(10), true, None).as_deref(),
        Some(base_digest.as_str()),
        "changing available compiler overflow semantics must change the claim digest"
    );
    let targeted_digest =
        exact_vc_claim_digest_sha256(&test_vc(10), false, Some("aarch64-apple-darwin;ptr64"));
    assert_ne!(
        targeted_digest.as_deref(),
        Some(base_digest.as_str()),
        "changing available compiler target identity must change the claim digest"
    );
}

#[test]
fn exact_vc_claim_digest_canonicalizes_state_machine_label_map_order() {
    let vc_with_label_order = |order: &[usize]| {
        let mut labels = trust_types::fx::FxHashMap::default();
        for state in order {
            labels.insert(*state, vec![format!("state_{state}"), format!("property_{state}")]);
        }
        VerificationCondition {
            kind: VcKind::Temporal {
                property: "AG !bad".to_string(),
                machine: Some(trust_types::StateMachineMetadata {
                    states: vec!["ready".to_string(), "running".to_string(), "bad".to_string()],
                    init_states: vec![0],
                    transitions: vec![(0, "start".to_string(), 1), (1, "fail".to_string(), 2)],
                    labels,
                }),
            },
            ..test_vc(10)
        }
    };

    let forward = vc_with_label_order(&[0, 1, 2]);
    let reverse = vc_with_label_order(&[2, 1, 0]);
    assert_eq!(
        exact_vc_key(&forward).map(|key| key.canonical_payload),
        exact_vc_key(&reverse).map(|key| key.canonical_payload),
        "equivalent unordered label maps must have one exact canonical identity"
    );
    let digest = exact_vc_claim_digest_sha256(&forward, false, None);
    assert_eq!(
        digest,
        exact_vc_claim_digest_sha256(&reverse, false, None),
        "equivalent unordered label maps must publish the same claim digest"
    );

    let mut changed = reverse;
    let VcKind::Temporal { machine: Some(machine), .. } = &mut changed.kind else {
        panic!("test fixture must retain its temporal state machine");
    };
    machine.labels.insert(1, vec!["different".to_string()]);
    assert_ne!(
        digest,
        exact_vc_claim_digest_sha256(&changed, false, None),
        "changing label content must still change the exact claim digest"
    );
}

fn test_binding_for_obligation(
    index: usize,
    vc: &VerificationCondition,
    obligation: &trust_verifier_api::TrustObligation,
) -> Option<ResultObligationBinding> {
    result_obligation_binding(index, vc, obligation)
}

fn bound_full_transport_results_for_test(
    overflow_checks: bool,
    function: &trust_types::VerifiableFunction,
    bundle: &trust_verifier_api::TrustContractBundle,
    run: &trust_verifier_api::VerificationRunResult,
) -> Vec<TransportObligationResult> {
    let (results, bindings) = full_verification_legacy_results_bound(function, bundle, run);
    let cleancic = (0..results.len()).map(|_| None).collect::<Vec<_>>();
    let authorities = build_result_proof_authorities(&results, &bindings, Some(run), &cleancic);
    build_transport_results_with_runtime_checks_bound(
        overflow_checks,
        None,
        &results,
        Some(run),
        &cleancic,
        &bindings,
        &authorities,
    )
}

#[test]
fn mir_dump_filenames_do_not_alias_sanitized_definition_paths() {
    let body = r#"{"def_path":"placeholder"}"#;
    let nested = mir_dump_filename("crate::a::b", body);
    let underscores = mir_dump_filename("crate::a__b", body);

    assert_ne!(nested, underscores, "distinct definition paths must not overwrite evidence");
    assert_eq!(nested, mir_dump_filename("crate::a::b", body));
    assert_ne!(nested, mir_dump_filename("crate::a::b", "different body"));
    assert!(nested.starts_with("trust-mir-"));
    assert!(nested.ends_with(".json"));
}

#[test]
fn mir_dump_publication_reuses_only_identical_regular_files() {
    let root = private_proof_store_test_root("mir-dump-reuse");
    let path = root.join("body.json");
    assert!(write_mir_dump_create_new(&path, "{\"body\":1}").expect("create dump"));
    assert!(!write_mir_dump_create_new(&path, "{\"body\":1}").expect("reuse identical dump"));
    assert!(
        write_mir_dump_create_new(&path, "{\"body\":2}").is_err(),
        "content-addressed publication must reject different pre-existing bytes"
    );
    std::fs::remove_dir_all(root).expect("remove MIR dump test root");
}

#[cfg(unix)]
#[test]
fn mir_dump_publication_never_reuses_a_leaf_symlink() {
    use std::os::unix::fs::symlink;

    let root = private_proof_store_test_root("mir-dump-symlink");
    let outside = root.join("outside.json");
    std::fs::write(&outside, "{\"body\":1}").expect("write symlink target");
    let path = root.join("body.json");
    symlink(&outside, &path).expect("create leaf symlink");

    let error = write_mir_dump_create_new(&path, "{\"body\":1}")
        .expect_err("identical bytes behind a symlink must not be accepted as published evidence");
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
    assert_eq!(
        std::fs::read_to_string(&outside).expect("read symlink target"),
        "{\"body\":1}",
        "rejected publication must not alter the symlink target"
    );
    std::fs::remove_dir_all(root).expect("remove MIR dump symlink test root");
}

#[test]
fn native_verification_gap_never_masquerades_as_vacuous_proof() {
    let gap = transport_native_verification_gap_row();
    assert_eq!(gap.kind, "native-verification-gap");
    assert_eq!(gap.outcome, Outcome::Unknown);
    assert!(gap.claim_digest_sha256.is_none());
    assert!(gap.proof_evidence.is_none());
    assert_ne!(gap.kind, "no_obligations");

    let vacuous = transport_no_obligations_row();
    assert_eq!(vacuous.kind, "no_obligations");
    assert_eq!(vacuous.outcome, Outcome::Proved);
    assert!(vacuous.claim_digest_sha256.is_none());
    assert!(
        vacuous.proof_evidence.is_none(),
        "a synthetic zero-obligation marker is structural bookkeeping, not a CleanCic proof"
    );
}

#[test]
fn assumption_reason_classes_distinguish_user_authority_from_capability_gaps() {
    assert_eq!(assumption_reason_class("user-opt-out"), "explicit user opt-out");
    assert_eq!(assumption_reason_class("unreachable-start"), "verification policy assumption");
    assert_eq!(assumption_reason_class("pattern-type"), "verifier capability gap");
}

fn test_transport_native_trust_ir() -> trust_types::TransportNativeTrustIrEvidence {
    trust_types::TransportNativeTrustIrEvidence {
        suite: "trust-wp".to_string(),
        backend: "trust-full-verifier".to_string(),
        request_id: Some("req-cache".to_string()),
        native_id: Some("native-cache".to_string()),
        present: true,
        artifacts: Vec::new(),
        diagnostics: Vec::new(),
    }
}

fn test_transport_proof_evidence() -> trust_types::TransportProofEvidence {
    let strength = ProofStrength::deductive();
    trust_types::TransportProofEvidence {
        suite: "trust-wp".to_string(),
        backend: "trust-full-verifier".to_string(),
        request_id: Some("req-cache".to_string()),
        proof_id: Some("proof-cache".to_string()),
        native_id: Some("native-cache".to_string()),
        status: TransportProofStatus::Proved,
        strength: Some(strength.clone()),
        evidence: Some(trust_types::ProofEvidence::from(strength)),
        artifacts: Vec::new(),
        diagnostics: Vec::new(),
    }
}

#[test]
fn normal_transport_rejects_unbound_solver_proved_label() {
    // A public result/strength label is not proof authority. Without an exact
    // CleanCic term or accepted native obligation binding, the row retains its
    // runtime check rather than reporting a proof.
    let proved = VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let rows =
        build_transport_results_with_runtime_checks(true, &[(test_vc(10), proved)], None, None);

    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
    assert_eq!(rows[0].solver, "ay");
    assert!(
        rows[0].reason.as_deref().is_some_and(|reason| {
            reason.contains("without exact kernel/native proof authority")
        })
    );
}

#[test]
fn unsupported_mir_transport_fails_closed_even_with_kernel_authority() {
    let bv = |value: i128| Box::new(Formula::BitVec { value, width: 8 });
    let unsupported_kind = VcKind::UnsupportedMir {
        kind: "FullVerification::OpaqueSemanticGap".to_string(),
        detail: "the preserved MIR operation has no exact verifier semantics".to_string(),
    };
    let vc = VerificationCondition {
        kind: unsupported_kind.clone(),
        function: trust_types::Symbol::intern("test::unsupported_transport"),
        location: trust_types::SourceSpan {
            file: "unsupported.rs".to_string(),
            line_start: 7,
            col_start: 3,
            line_end: 7,
            col_end: 19,
        },
        // This contradiction is deliberately in the CleanCic-supported
        // fragment. It proves that valid proof authority still cannot upgrade
        // an explicitly unsupported semantic translation.
        formula: Formula::And(vec![
            Formula::BvULt(bv(3), bv(7), 8),
            Formula::BvULt(bv(7), bv(3), 8),
        ]),
        contract_metadata: None,
    };
    let results = vec![(
        vc,
        VerificationResult::Proved {
            solver: trust_types::Symbol::intern("ay"),
            time_ms: 4,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let cleancic = certify_all(&results, None);
    assert!(matches!(cleancic.as_slice(), [Some(trust_ir::ProofEvidence::CleanCic { .. })]));
    let authorities = build_result_proof_authorities(&results, &[None], None, &cleancic);
    assert!(matches!(authorities.as_slice(), [Some(ResultProofAuthority::KernelCertified { .. })]));

    let rows = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        None,
        &cleancic,
        &[],
        &authorities,
    );
    let row = &rows[0];
    assert_eq!(row.outcome, Outcome::Unknown);
    assert_eq!(row.reason.as_deref(), Some(TRUST_UNSUPPORTED_MIR_TRANSPORT_REASON));
    assert_eq!(row.typed_kind.as_deref(), Some(&unsupported_kind));
    assert_eq!(row.kind, unsupported_kind.transport_tag());
    assert_eq!(row.description, unsupported_kind.description());
    assert!(
        row.proof_evidence.is_some(),
        "the independent kernel artifact remains available as diagnostic evidence"
    );

    // Exercise the same final boundary against a future producer accidentally
    // assigning a runtime fallback to UnsupportedMir.
    let mut future_outcome = Outcome::RuntimeChecked;
    let mut future_reason = Some("future producer supplied a fallback".to_string());
    fail_closed_unsupported_mir_transport_outcome(
        &unsupported_kind,
        &mut future_outcome,
        &mut future_reason,
    );
    assert_eq!(future_outcome, Outcome::Unknown);
    assert!(future_reason.as_deref().is_some_and(|reason| {
        reason.starts_with(TRUST_UNSUPPORTED_MIR_TRANSPORT_REASON)
            && reason.contains("future producer supplied a fallback")
    }));
}

/// M-Pkg live-path: a Certified obligation's transport row carries the
/// kernel-checked CleanCic proof term as a `clean_cic` evidence artifact, with
/// matching Constructive+Certified strength/evidence metadata. Uses a QF-BV
/// bvult-antisymmetry obligation `(bvult 3 7) ∧ (bvult 7 3)` that `certify_vc`
/// kernel-certifies.
#[test]
fn certified_row_carries_clean_cic_artifact_and_constructive_certified_metadata() {
    let bv = |v: i128| Box::new(trust_types::Formula::BitVec { value: v, width: 8 });
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: trust_types::Symbol::intern("test::certified"),
        location: trust_types::SourceSpan {
            file: "t.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 5,
        },
        formula: trust_types::Formula::And(vec![
            trust_types::Formula::BvULt(bv(3), bv(7), 8),
            trust_types::Formula::BvULt(bv(7), bv(3), 8),
        ]),
        contract_metadata: None,
    };
    let proved = VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let rows = build_transport_results_with_runtime_checks(false, &[(vc, proved)], None, None);
    assert_eq!(rows.len(), 1);
    let pe = rows[0]
        .proof_evidence
        .as_ref()
        .expect("a Certified obligation's row must carry proof_evidence");
    let expected_strength = ProofStrength {
        reasoning: ReasoningKind::Constructive,
        assurance: trust_types::AssuranceLevel::Certified,
    };
    assert_eq!(pe.status, TransportProofStatus::Proved);
    assert_eq!(pe.strength.as_ref(), Some(&expected_strength));
    assert_eq!(
        pe.evidence.as_ref(),
        Some(&trust_types::ProofEvidence::from(expected_strength)),
        "ProofStrength and ProofEvidence must describe the same kernel-certified constructive proof"
    );
    assert_eq!(pe.artifacts.len(), 1, "CleanCic publication has one exact payload artifact");
    let artifact = &pe.artifacts[0];
    assert_eq!(artifact.kind, "clean_cic");
    let payload = artifact.metadata.as_ref().expect("CleanCic payload metadata");
    let bytes = serde_json::to_vec(payload).expect("serialize exact CleanCic payload");
    let digest = domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
    let expected_id = format!("clean-cic:v2:{digest}");
    assert_eq!(pe.proof_id.as_deref(), Some(expected_id.as_str()));
    assert_eq!(artifact.artifact_id.as_deref(), pe.proof_id.as_deref());
    assert_eq!(
        artifact.digest.as_ref(),
        Some(&TransportArtifactDigest { algorithm: "sha256".into(), value: digest.clone() })
    );
    let expected_uri = format!("trust-certify://clean-cic/{digest}");
    assert_eq!(artifact.uri.as_deref(), Some(expected_uri.as_str()));
}

/// M-Pkg perf: the precomputed-certification path (`certify_all` →
/// `build_transport_results_with_runtime_checks(.., Some(&cleancic))`) ships the
/// SAME `clean_cic` artifact the per-row fallback path produces. This proves the
/// dedup (kernel runs once, shared by both builders) is behavior-preserving: the
/// label never out-runs the proof, and threading the term changes nothing a
/// consumer sees.
#[test]
fn precomputed_certification_matches_fallback_clean_cic_artifact() {
    let bv = |v: i128| Box::new(trust_types::Formula::BitVec { value: v, width: 8 });
    let make_vc = || VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: trust_types::Symbol::intern("test::certified"),
        location: trust_types::SourceSpan {
            file: "t.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 5,
        },
        formula: trust_types::Formula::And(vec![
            trust_types::Formula::BvULt(bv(3), bv(7), 8),
            trust_types::Formula::BvULt(bv(7), bv(3), 8),
        ]),
        contract_metadata: None,
    };
    let make_proved = || VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };

    let results = vec![(make_vc(), make_proved())];
    let cleancic = certify_all(&results, None);
    // The bvult-antisymmetry obligation kernel-certifies, so `certify_all`
    // populates a `Some(CleanCic)` entry index-aligned with `results`.
    assert_eq!(cleancic.len(), 1);
    assert!(
        matches!(cleancic[0], Some(trust_ir::ProofEvidence::CleanCic { .. })),
        "certify_all must kernel-certify the bvult-antisymmetry obligation"
    );

    let clean_cic_meta = |rows: &[TransportObligationResult]| {
        let pe = rows[0]
            .proof_evidence
            .as_ref()
            .expect("a Certified obligation's row must carry proof_evidence");
        pe.artifacts
            .iter()
            .find(|a| a.kind == "clean_cic")
            .expect("row must carry a clean_cic artifact")
            .metadata
            .clone()
    };

    let precomputed =
        build_transport_results_with_runtime_checks(false, &results, None, Some(&cleancic));
    let fallback = build_transport_results_with_runtime_checks(false, &results, None, None);

    // Same proof term, whichever path produced it.
    assert_eq!(clean_cic_meta(&precomputed), clean_cic_meta(&fallback));
}

/// A solver-owned `Proved` carrier need not be rewritten before the independent
/// Clean kernel can certify its exact VC. In particular, retaining the native
/// solver metadata is compatible with minting the stronger private kernel
/// authority from `certify_all`'s separately re-checked CleanCic evidence.
#[test]
fn kernel_authority_certifies_sound_summand_bounded_proved_without_mutating_solver_result() {
    let var = |name: &str| trust_types::Formula::Var(name.to_string(), trust_types::Sort::Int);
    let int = trust_types::Formula::Int;
    let le = |lhs, rhs| trust_types::Formula::Le(Box::new(lhs), Box::new(rhs));
    let lt = |lhs, rhs| trust_types::Formula::Lt(Box::new(lhs), Box::new(rhs));
    let gt = |lhs, rhs| trust_types::Formula::Gt(Box::new(lhs), Box::new(rhs));
    let add = |lhs, rhs| trust_types::Formula::Add(Box::new(lhs), Box::new(rhs));
    let half_u32_max = 2_147_483_647;
    let u32_max = 4_294_967_295;
    let midpoint_sum = || add(var("_4"), var("_6"));
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (trust_types::Ty::u32(), trust_types::Ty::u32()),
        },
        function: trust_types::Symbol::intern("test::summand_bounded_midpoint"),
        location: trust_types::SourceSpan {
            file: "midpoint.rs".to_string(),
            line_start: 7,
            col_start: 9,
            line_end: 7,
            col_end: 22,
        },
        formula: trust_types::Formula::And(vec![
            le(int(0), var("_4")),
            le(var("_4"), int(half_u32_max)),
            le(int(0), var("_6")),
            le(var("_6"), int(half_u32_max)),
            trust_types::Formula::Or(vec![
                lt(midpoint_sum(), int(0)),
                gt(midpoint_sum(), int(u32_max)),
            ]),
        ]),
        contract_metadata: None,
    };

    let original_solver = trust_types::Symbol::intern("trust-mc-chc");
    let original_strength = ProofStrength {
        reasoning: ReasoningKind::ChcSpacer,
        assurance: trust_types::AssuranceLevel::Sound,
    };
    let original_certificate = b"retained native solver certificate".to_vec();
    let original_warnings = vec!["retained native solver warning".to_string()];
    let results = vec![(
        vc,
        VerificationResult::Proved {
            solver: original_solver,
            time_ms: 37,
            strength: original_strength.clone(),
            proof_certificate: Some(original_certificate.clone()),
            solver_warnings: Some(original_warnings.clone()),
            native_proof_envelope: None,
        },
    )];

    let cleancic = certify_all(&results, None);
    assert!(matches!(cleancic.as_slice(), [Some(trust_ir::ProofEvidence::CleanCic { .. })]));
    let authorities = build_result_proof_authorities(&results, &[None], None, &cleancic);
    assert!(matches!(authorities.as_slice(), [Some(ResultProofAuthority::KernelCertified { .. })]));

    let VerificationResult::Proved {
        solver,
        time_ms,
        strength,
        proof_certificate,
        solver_warnings,
        native_proof_envelope,
    } = &results[0].1
    else {
        panic!("kernel certification must not replace the solver's Proved carrier");
    };
    assert_eq!(solver, &original_solver);
    assert_eq!(*time_ms, 37);
    assert_eq!(strength, &original_strength);
    assert_eq!(proof_certificate.as_deref(), Some(original_certificate.as_slice()));
    assert_eq!(solver_warnings.as_ref(), Some(&original_warnings));
    assert_eq!(native_proof_envelope, &None);
}

/// M-Pkg perf: `certify_all` is fail-closed — it attempts kernel certification
/// only for `Proved` results and never invokes the kernel for a `Failed` (or any
/// non-Proved) obligation, mapping it to `None`.
#[test]
fn certify_all_skips_non_proved_results() {
    let vc = test_vc(10);
    let failed = VerificationResult::Failed {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        counterexample: None,
    };
    let cleancic = certify_all(&[(vc, failed)], None);
    assert_eq!(cleancic.len(), 1);
    assert!(cleancic[0].is_none(), "a Failed obligation must never be certified");
}

/// Trust (M5 blocker #0): once the deadline has passed, `certify_all` stops
/// invoking the kernel for any further `Proved` obligation in the slice — each
/// maps to `None` exactly as a naturally-uncertifiable obligation would, so a
/// slow/degraded run can only lose "Certified" evidence, never fabricate it.
#[test]
fn certify_all_stops_after_deadline_elapsed() {
    let bv = |v: i128| Box::new(trust_types::Formula::BitVec { value: v, width: 8 });
    let make_vc = || VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: trust_types::Symbol::intern("test::certified"),
        location: trust_types::SourceSpan {
            file: "t.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 5,
        },
        formula: trust_types::Formula::And(vec![
            trust_types::Formula::BvULt(bv(3), bv(7), 8),
            trust_types::Formula::BvULt(bv(7), bv(3), 8),
        ]),
        contract_metadata: None,
    };
    let make_proved = || VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let results = vec![(make_vc(), make_proved()), (make_vc(), make_proved())];

    // A deadline already in the past: the kernel must never be invoked, for
    // either obligation, even though both are individually kernel-certifiable
    // (see `precomputed_certification_matches_fallback_clean_cic_artifact`).
    let already_elapsed = std::time::Instant::now() - std::time::Duration::from_secs(1);
    let cleancic = certify_all(&results, Some(already_elapsed));
    assert_eq!(cleancic.len(), 2);
    assert!(
        cleancic.iter().all(Option::is_none),
        "an elapsed deadline must skip kernel certification for every remaining obligation, got {cleancic:?}"
    );
}

/// Trust (M5 blocker #0): the promotion counterpart — an already-elapsed
/// deadline must leave every inconclusive obligation exactly as it arrived
/// (never upgraded to `Proved`), even though the kernel could certify it.
#[test]
fn promote_kernel_certifiable_stops_after_deadline_elapsed() {
    let bv = |v: i128| Box::new(trust_types::Formula::BitVec { value: v, width: 8 });
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: trust_types::Symbol::intern("test::inconclusive"),
        location: trust_types::SourceSpan {
            file: "t.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 5,
        },
        formula: trust_types::Formula::And(vec![
            trust_types::Formula::BvULt(bv(3), bv(7), 8),
            trust_types::Formula::BvULt(bv(7), bv(3), 8),
        ]),
        contract_metadata: None,
    };
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        reason: "test".to_string(),
    };
    let mut results = vec![(vc, unknown)];

    let already_elapsed = std::time::Instant::now() - std::time::Duration::from_secs(1);
    promote_kernel_certifiable(&mut results, Some(already_elapsed));
    assert!(
        matches!(results[0].1, VerificationResult::Unknown { .. }),
        "an elapsed deadline must leave an inconclusive obligation un-upgraded, got {:?}",
        results[0].1
    );
}

#[test]
fn legacy_vc_preserves_contract_specific_unsupported_obligation_identity() {
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "obligation:demo:f:unsupported:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.contract".to_string(),
            name: "unsupported".to_string(),
        },
        contract_id: Some("contract:demo:f:requires:0".to_string()),
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "unsupported contract predicate".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![trust_verifier_api::MetadataEntry {
            key: "trust.contract.unsupported_reason".to_string(),
            value: "not lowered".to_string(),
        }],
    };

    let (kind, detail) = legacy_unsupported_kind_detail(&obligation);

    assert_eq!(kind, "FullVerification::trust.contract::unsupported");
    assert!(detail.contains("contract_id=contract:demo:f:requires:0"));
    assert!(detail.contains("metadata_keys=[trust.contract.unsupported_reason]"));
}

#[test]
fn full_verification_unsupported_ensures_recognizer_is_structural() {
    let kind = "FullVerification::trust.contract::unsupported";

    assert!(is_full_verification_unsupported_ensures(
        kind,
        "unsupported contract predicate; contract_id=trust-contract:demo::f:ensures:0"
    ));
    assert!(is_full_verification_unsupported_ensures(
        kind,
        "unsupported contract predicate; contract_id=trust-contract:demo::f:ensures:12; metadata_keys=[trust.contract.unsupported_reason]"
    ));

    assert!(!is_full_verification_unsupported_ensures(
        kind,
        "unsupported contract predicate; contract_id=trust-contract:demo::f:requires:0"
    ));
    assert!(!is_full_verification_unsupported_ensures(
        kind,
        "unsupported contract predicate; contract_id=trust-contract:demo::f:ensures:not-a-number"
    ));
    assert!(!is_full_verification_unsupported_ensures(
        "FullVerification::trust.contract::different",
        "unsupported contract predicate; contract_id=trust-contract:demo::f:ensures:0"
    ));
    assert!(!is_full_verification_unsupported_ensures(
        kind,
        "source lookalike; contract_id=trust-contract:demo::f:ensures:0; contract_id=trust-contract:demo::f:requires:1"
    ));

    assert!(is_spec_ensures_unparseable_obligation("SpecEnsuresUnparseable", "compiler detail"));
    assert!(is_spec_ensures_unparseable_obligation(
        "FullVerification::trust.vc::unsupported_mir",
        "unsupported MIR `SpecEnsuresUnparseable`: compiler detail"
    ));
    assert!(!is_spec_ensures_unparseable_obligation(
        "SourceSpecEnsuresUnparseableLookalike",
        "compiler detail"
    ));
    assert!(!is_spec_ensures_unparseable_obligation(
        "FullVerification::trust.vc::unsupported_mir",
        "source lookalike `SpecEnsuresUnparseable` after an unrelated prefix"
    ));
}

#[test]
fn full_verifier_hardened_api_obligation_round_trips_to_hardened_vc_kind() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo__checked_transfer:hardened_boundary:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.hardened".to_string(),
            name: "panic_boundary".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "hardened boundary (panic_boundary): unwrap: success must be proven"
            .to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_HARDENED_CATEGORY_METADATA_KEY.to_string(),
                value: "panic_boundary".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_HARDENED_CALLEE_METADATA_KEY.to_string(),
                value: "Option::unwrap".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_HARDENED_DETAIL_METADATA_KEY.to_string(),
                value: "success must be proven".to_string(),
            },
        ],
    };

    let vc = legacy_vc_from_api_obligation(&function, &obligation);

    assert!(matches!(
        &vc.kind,
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee,
            detail,
        } if callee.as_str() == "Option::unwrap" && detail.as_str() == "success must be proven"
    ));
    assert_eq!(format_vc_kind(&vc.kind), "hardened_panic_boundary");
    assert_eq!(
        convert_vc_kind(&vc.kind),
        TrustObligationKind::HardenedBoundary(TrustHardenedVcCategory::PanicBoundary)
    );
}

#[test]
fn full_verifier_hardened_custom_name_reconstructs_without_private_metadata() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo__checked_transfer:panic_boundary:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.hardened".to_string(),
            name: "panic_boundary".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "hardened boundary (panic_boundary): unwrap: success must be proven"
            .to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };

    let vc = legacy_vc_from_api_obligation(&function, &obligation);

    assert!(matches!(
        &vc.kind,
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee,
            ..
        } if callee.as_str() == "panic_boundary"
    ));
    assert_eq!(
        convert_vc_kind(&vc.kind),
        TrustObligationKind::HardenedBoundary(TrustHardenedVcCategory::PanicBoundary)
    );
}

#[test]
fn full_verifier_unknown_hardened_custom_name_stays_first_class() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo__checked_transfer:new_future_category:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.hardened".to_string(),
            name: "new_future_category".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "future hardened boundary".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };

    let vc = legacy_vc_from_api_obligation(&function, &obligation);

    let VcKind::HardenedBoundary { category, callee, detail } = &vc.kind else {
        panic!("expected hardened boundary, got {:?}", vc.kind);
    };
    assert!(category.is_unknown());
    assert_eq!(category.as_tag(), "new_future_category");
    assert_eq!(callee.as_str(), "new_future_category");
    assert!(detail.contains("new_future_category"));
    assert_eq!(format_vc_kind(&vc.kind), "hardened_new_future_category");
    rustc_span::create_session_if_not_set_then(rustc_span::edition::DEFAULT_EDITION, |_| {
        match convert_vc_kind(&vc.kind) {
            TrustObligationKind::HardenedBoundary(TrustHardenedVcCategory::Unknown(tag)) => {
                assert_eq!(tag.as_str(), "new_future_category");
            }
            other => panic!("expected unknown hardened boundary, got {other:?}"),
        }
    });
}

#[test]
fn unknown_overflow_is_runtime_checked_when_overflow_checks_are_on() {
    let kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
    };
    assert!(runtime_check_available(&kind, true));
}

#[test]
fn unknown_overflow_stays_unknown_when_overflow_checks_are_off() {
    let kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
    };
    assert!(!runtime_check_available(&kind, false));
}

#[test]
fn bounds_unknown_is_runtime_checked_even_without_overflow_checks() {
    assert!(runtime_check_available(&VcKind::IndexOutOfBounds, false));
}

#[test]
fn precondition_unknown_has_no_runtime_fallback() {
    assert!(
        !runtime_check_available(&VcKind::Precondition { callee: "callee".to_string() }, true,)
    );
}

#[test]
fn float_unknown_has_no_runtime_fallback() {
    assert!(!runtime_check_available(&VcKind::FloatDivisionByZero, true));
    assert!(!runtime_check_available(
        &VcKind::FloatOverflowToInfinity {
            op: BinOp::Add,
            operand_ty: trust_types::Ty::Float { width: 64 },
        },
        true,
    ));
}

#[test]
fn float_runtime_check_note_explains_no_dynamic_fallback() {
    assert_eq!(
        runtime_check_note(&VcKind::FloatDivisionByZero),
        "floating-point operations do not trap at runtime; no dynamic fallback exists",
    );
}

#[test]
fn unbounded_allocation_vc_tag_is_distinct_not_unknown() {
    // Regression: the leak/OOM-boundedness obligation must transport under its own
    // tag, not fall through to "unknown" where a leak-freedom survey can't find it.
    let kind = VcKind::UnboundedAllocation {
        callee: "Vec::with_capacity".to_string(),
        count: "n".to_string(),
        detail: "count `n` is not provably bounded".to_string(),
    };
    assert_eq!(format_vc_kind(&kind), "unbounded_allocation");
}

#[test]
fn full_lane_round_trip_rows_recover_their_real_kind_tag() {
    // Regression: the native round trip re-materializes a legacy VC as
    // `UnsupportedMir { kind: "FullVerification::<ApiKind>", detail }`
    // (`legacy_unsupported_kind_detail`); `format_vc_kind` had no arm for these
    // rows, so every full-lane obligation surveyed as "unknown" in both the
    // human report and the JSON `kind` field. The real kind is recovered from
    // the structured survivors: the API family in `kind`, cross-checked against
    // the original `VcKind::description()` text leading `detail`.
    let row = |kind: &str, detail: &str| VcKind::UnsupportedMir {
        kind: kind.to_string(),
        detail: detail.to_string(),
    };
    assert_eq!(
        format_vc_kind(&row(
            "FullVerification::ArithmeticSafety",
            "division by zero; contract_id=contract:trust-mc-typed-chc-public:0e43; \
             metadata_keys=[trust.vc.kind]",
        )),
        "divzero",
    );
    assert_eq!(
        format_vc_kind(&row("FullVerification::ArithmeticSafety", "arithmetic overflow (Add)")),
        "overflow:add",
    );
    assert_eq!(
        format_vc_kind(&row("FullVerification::ArithmeticSafety", "shift overflow (Shl)")),
        "shift:left",
    );
    assert_eq!(
        format_vc_kind(&row("FullVerification::ArithmeticSafety", "float division by zero")),
        "float_division_by_zero",
    );
    assert_eq!(
        format_vc_kind(&row("FullVerification::BoundsCheck", "index out of bounds")),
        "bounds",
    );
    assert_eq!(
        format_vc_kind(&row("FullVerification::Assertion", "unreachable code reached")),
        "unreach",
    );
    assert_eq!(
        format_vc_kind(&row("FullVerification::Precondition", "precondition of `reciprocal`")),
        "precond",
    );
    // Cross-check: a description that does not belong to the claimed API
    // family stays fail-closed "unknown" — recovery can never relabel a row
    // across families.
    assert_eq!(
        format_vc_kind(&row("FullVerification::BoundsCheck", "division by zero")),
        "unknown",
    );
    // A genuine unsupported-MIR VC round-tripped through the full lane has no
    // real kind to recover.
    assert_eq!(
        format_vc_kind(&row(
            "FullVerification::trust.vc::unsupported_mir",
            "unsupported MIR `SpecEnsuresUnparseable`: unparseable `#[ensures]` predicate",
        )),
        "unknown",
    );
    // A direct (default-lane) unsupported-MIR VC is untouched.
    assert_eq!(format_vc_kind(&row("SpecEnsuresUnparseable", "whatever")), "unknown");
}

#[test]
fn float_vc_tags_are_not_unknown() {
    assert_eq!(format_vc_kind(&VcKind::FloatDivisionByZero), "float_division_by_zero");
    assert_eq!(
        format_vc_kind(&VcKind::FloatOverflowToInfinity {
            op: BinOp::Add,
            operand_ty: trust_types::Ty::Float { width: 64 },
        }),
        "float_overflow_to_infinity",
    );
}

#[test]
fn transport_compact_kind_tags_stay_stable() {
    let cases = vec![
        (VcKind::DivisionByZero, "divzero"),
        (VcKind::RemainderByZero, "remzero"),
        (VcKind::SliceBoundsCheck, "slice"),
        (VcKind::Precondition { callee: "crate::callee".to_string() }, "precond"),
        (VcKind::Postcondition, "postcond"),
        (VcKind::Unreachable, "unreach"),
        (VcKind::Temporal { property: "□ safe".to_string(), machine: None }, "temporal"),
        (
            VcKind::TaintViolation {
                source_label: "request".to_string(),
                sink_kind: "shell".to_string(),
                path_length: 2,
            },
            "taint",
        ),
        (
            VcKind::ProtocolViolation {
                protocol: "two-phase-commit".to_string(),
                violation: "double commit".to_string(),
            },
            "protocol",
        ),
        (
            VcKind::NonTermination {
                context: "loop".to_string(),
                measure: "remaining".to_string(),
            },
            "termination",
        ),
        (
            VcKind::UnboundedAllocation {
                callee: "Vec::with_capacity".to_string(),
                count: "n".to_string(),
                detail: "no established allocation budget".to_string(),
            },
            "unbounded_allocation",
        ),
        (
            VcKind::DataRace {
                variable: "state".to_string(),
                thread_a: "writer".to_string(),
                thread_b: "reader".to_string(),
            },
            "unknown",
        ),
    ];

    for (kind, expected) in cases {
        assert_eq!(kind.transport_tag(), expected);
        assert_eq!(format_vc_kind(&kind), expected);
    }
}

#[test]
fn hardened_vc_tags_are_transport_visible() {
    let kind = VcKind::HardenedBoundary {
        category: HardenedVcCategory::PanicBoundary,
        callee: "mir_assert::BoundsCheck".to_string(),
        detail: "MIR bounds-check assert can panic".to_string(),
    };

    assert_eq!(format_vc_kind(&kind), "hardened_panic_boundary");
    assert_eq!(
        convert_vc_kind(&kind),
        TrustObligationKind::HardenedBoundary(TrustHardenedVcCategory::PanicBoundary)
    );
    assert_eq!(convert_proof_level(&kind), TrustProofLevel::L1Functional);
}

#[test]
fn native_unsafe_and_ffi_hardened_categories_round_trip_to_internal_categories() {
    let unsafe_kind = VcKind::UnsafeOperation { desc: "raw pointer deref".to_string() };
    let ffi_kind = VcKind::FfiBoundaryViolation {
        callee: "strlen".to_string(),
        desc: "trusted wrapper contract required".to_string(),
    };

    assert_eq!(format_vc_kind(&unsafe_kind), "hardened_unsafe_operation");
    assert_eq!(format_vc_kind(&ffi_kind), "hardened_ffi_boundary");
    assert_eq!(
        convert_vc_kind(&unsafe_kind),
        TrustObligationKind::HardenedBoundary(TrustHardenedVcCategory::UnsafeOperation)
    );
    assert_eq!(
        convert_vc_kind(&ffi_kind),
        TrustObligationKind::HardenedBoundary(TrustHardenedVcCategory::FfiBoundary)
    );
    assert_eq!(convert_proof_level(&unsafe_kind), TrustProofLevel::L0Safety);
    assert_eq!(convert_proof_level(&ffi_kind), TrustProofLevel::L0Safety);
}

#[test]
fn unknown_hardened_category_converts_to_internal_unknown() {
    rustc_span::create_default_session_globals_then(|| {
        let converted =
            convert_hardened_category(HardenedVcCategory::unknown_tag("future_hardened_category"));

        match converted {
            TrustHardenedVcCategory::Unknown(tag) => {
                assert_eq!(tag.as_str(), "future_hardened_category");
            }
            other => panic!("expected unknown hardened category, got {other:?}"),
        }
    });
}

#[test]
fn hardened_obligation_fingerprint_includes_detail_and_formula() {
    let base = VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "Option::unwrap".to_string(),
            detail: "success must be proven".to_string(),
        },
        function: trust_types::Symbol::intern("test::f"),
        location: trust_types::SourceSpan {
            file: "test.rs".to_string(),
            line_start: 10,
            col_start: 1,
            line_end: 10,
            col_end: 12,
        },
        formula: trust_types::Formula::Bool(false),
        contract_metadata: None,
    };
    let mut changed_detail = base.clone();
    changed_detail.kind = VcKind::HardenedBoundary {
        category: HardenedVcCategory::PanicBoundary,
        callee: "Option::unwrap".to_string(),
        detail: "different precondition".to_string(),
    };
    let mut changed_formula = base.clone();
    changed_formula.formula = trust_types::Formula::Bool(true);
    let mut changed_location = base.clone();
    changed_location.location = trust_types::SourceSpan {
        file: "moved.rs".to_string(),
        line_start: 99,
        col_start: 7,
        line_end: 99,
        col_end: 20,
    };

    assert_ne!(
        compute_obligation_fingerprint(&base),
        compute_obligation_fingerprint(&changed_detail)
    );
    assert_ne!(
        compute_obligation_fingerprint(&base),
        compute_obligation_fingerprint(&changed_formula)
    );
    assert_eq!(
        compute_obligation_fingerprint(&base),
        compute_obligation_fingerprint(&changed_location)
    );
}

#[test]
fn internal_proof_levels_match_trust_types_for_non_l0_kinds() {
    assert_eq!(TrustObligationKind::NonTermination.proof_level(), TrustProofLevel::L1Functional);
    assert_eq!(TrustObligationKind::TaintViolation.proof_level(), TrustProofLevel::L1Functional);
    assert_eq!(
        TrustObligationKind::ResilienceViolation.proof_level(),
        TrustProofLevel::L1Functional
    );
    assert_eq!(TrustObligationKind::Deadlock.proof_level(), TrustProofLevel::L2Domain);
}

#[test]
fn unmapped_vc_kinds_fallback_by_trust_types_proof_level() {
    assert_eq!(
        convert_vc_kind(&VcKind::FunctionalCorrectness {
            property: "state matches spec".to_string(),
            context: "post-state".to_string(),
        }),
        TrustObligationKind::Postcondition
    );
}

#[test]
fn float_vc_kinds_map_to_existing_internal_obligation_buckets() {
    assert_eq!(convert_vc_kind(&VcKind::FloatDivisionByZero), TrustObligationKind::DivisionByZero,);
    assert_eq!(
        convert_vc_kind(&VcKind::FloatOverflowToInfinity {
            op: BinOp::Add,
            operand_ty: trust_types::Ty::Float { width: 64 },
        }),
        TrustObligationKind::ArithmeticOverflow(TrustBinOp::Add),
    );
}

#[test]
fn arithmetic_overflow_binops_are_exact_and_unknown_categories_fail_closed() {
    for (source, expected) in [
        (BinOp::Add, TrustBinOp::Add),
        (BinOp::Sub, TrustBinOp::Sub),
        (BinOp::Mul, TrustBinOp::Mul),
        (BinOp::Div, TrustBinOp::Div),
        (BinOp::Rem, TrustBinOp::Rem),
        (BinOp::Shl, TrustBinOp::Shl),
        (BinOp::Shr, TrustBinOp::Shr),
    ] {
        assert_eq!(convert_binop(&source), Some(expected));
        assert_eq!(
            convert_vc_kind(&VcKind::ArithmeticOverflow {
                op: source,
                operand_tys: (trust_types::Ty::i32(), trust_types::Ty::i32()),
            }),
            TrustObligationKind::ArithmeticOverflow(expected),
        );
    }

    for unsupported in [
        BinOp::Eq,
        BinOp::Ne,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::BitAnd,
        BinOp::BitOr,
        BinOp::BitXor,
        BinOp::Cmp,
    ] {
        assert_eq!(convert_binop(&unsupported), None);
        assert_eq!(
            convert_vc_kind(&VcKind::ArithmeticOverflow {
                op: unsupported,
                operand_tys: (trust_types::Ty::i32(), trust_types::Ty::i32()),
            }),
            TrustObligationKind::UnsupportedMir,
            "malformed overflow VC for {unsupported:?} must not alias Add",
        );
    }
}

#[test]
fn telemetry_carries_runtime_fallback_metadata() {
    let mut details: IndexVec<ObligationId, TrustObligationDetail> = IndexVec::new();
    details.push(TrustObligationDetail {
        solver: rustc_span::sym::test,
        time_us: 5_000,
        counterexample: vec![],
        runtime_fallback: Some(runtime_fallback_detail(
            RuntimeFallbackOutcome::Unknown,
            "solver could not decide",
        )),
    });
    details.push(TrustObligationDetail {
        solver: rustc_span::sym::test,
        time_us: 7_000,
        counterexample: vec![],
        runtime_fallback: None,
    });
    let telemetry = TrustProofTelemetry { details };
    assert_eq!(telemetry.runtime_checked_count(), 1);

    let mut runtime_checked = telemetry.runtime_checked_details();
    let (obligation, detail) = runtime_checked.next().expect("runtime-checked detail");
    assert_eq!(obligation.index(), 0);
    assert!(detail.is_runtime_checked());

    let fallback = detail.runtime_fallback().expect("runtime fallback metadata");
    assert_eq!(fallback.reason, TrustRuntimeFallbackReason::Unknown);
    assert!(fallback.note.contains("solver returned unknown"));

    let second = telemetry.detail(obligation).expect("detail lookup");
    assert_eq!(second.solver, detail.solver);
    assert!(runtime_checked.next().is_none());
    assert!(telemetry.detail(obligation).unwrap().runtime_fallback().is_some());
}

#[test]
fn runtime_fallback_detail_uses_timeout_reason() {
    let fallback = runtime_fallback_detail(RuntimeFallbackOutcome::Timeout, "solver timed out");
    assert_eq!(fallback.reason, TrustRuntimeFallbackReason::Timeout);
    assert_eq!(fallback.note, "solver timed out");
}

#[test]
fn telemetry_ignores_non_runtime_checked_obligations() {
    let mut details: IndexVec<ObligationId, TrustObligationDetail> = IndexVec::new();
    details.push(TrustObligationDetail {
        solver: rustc_span::sym::test,
        time_us: 12_000,
        counterexample: vec![],
        runtime_fallback: None,
    });
    let telemetry = TrustProofTelemetry { details };
    assert_eq!(telemetry.runtime_checked_count(), 0);
    assert!(telemetry.runtime_checked_details().next().is_none());
    assert!(telemetry.details[ObligationId::from_usize(0)].runtime_fallback().is_none());
}

fn proof_results_with_statuses(statuses: &[TrustStatus]) -> TrustProofResults {
    let mut dispositions: IndexVec<ObligationId, TrustDisposition> = IndexVec::new();
    let mut fingerprints: IndexVec<ObligationId, Fingerprint> = IndexVec::new();

    for status in statuses {
        dispositions.push(TrustDisposition {
            kind: TrustObligationKind::DivisionByZero,
            status: *status,
            strength: match status {
                TrustStatus::Certified => TrustProofStrength::Constructive,
                TrustStatus::Trusted => TrustProofStrength::SmtUnsat,
                _ => TrustProofStrength::None,
            },
            certified: matches!(status, TrustStatus::Certified),
        });
        fingerprints.push(Fingerprint::ZERO);
    }

    let summary = TrustFunctionSummary::from_dispositions(&dispositions);
    TrustProofResults { dispositions, fingerprints, summary }
}

#[test]
fn proof_results_full_verification_rejects_zero_obligations() {
    let results = proof_results_with_statuses(&[]);

    assert!(!results.summary.is_fully_verified());
    assert!(!results.is_fully_verified());
}

#[test]
fn proof_results_full_verification_rejects_unaccounted_summary_total() {
    let mut results = proof_results_with_statuses(&[TrustStatus::Trusted]);
    results.summary.total = 2;

    assert!(!results.summary.is_fully_verified());
    assert!(!results.is_fully_verified());
}

#[test]
fn proof_results_full_verification_rejects_misaligned_obligation_arrays() {
    let mut results = proof_results_with_statuses(&[TrustStatus::Trusted]);
    results.fingerprints = IndexVec::new();

    assert!(results.summary.is_fully_verified());
    assert!(!results.is_fully_verified());
}

#[test]
fn proof_results_full_verification_accepts_accounted_static_obligations() {
    let results = proof_results_with_statuses(&[TrustStatus::Trusted, TrustStatus::Certified]);

    assert!(results.summary.is_fully_verified());
    assert!(results.is_fully_verified());
}

#[test]
fn dyn_summary_proof_gate_requires_nonzero_accounted_static_obligations() {
    let zero = proof_results_with_statuses(&[]);
    assert!(!has_nonzero_accounted_static_proof(&zero));

    let mut unaccounted = proof_results_with_statuses(&[TrustStatus::Trusted]);
    unaccounted.summary.total = 2;
    assert!(!has_nonzero_accounted_static_proof(&unaccounted));

    let mut misaligned = proof_results_with_statuses(&[TrustStatus::Trusted]);
    misaligned.fingerprints = IndexVec::new();
    assert!(!has_nonzero_accounted_static_proof(&misaligned));

    let verified = proof_results_with_statuses(&[TrustStatus::Trusted]);
    assert!(has_nonzero_accounted_static_proof(&verified));
}

#[test]
fn dedupe_exact_vcs_drops_duplicate_slot() {
    let vc = test_vc(10);
    let deduped = dedupe_exact_vcs(vec![vc.clone(), vc]);
    assert_eq!(deduped.len(), 1);
}

#[test]
fn dedupe_exact_vcs_preserves_distinct_spans() {
    let deduped = dedupe_exact_vcs(vec![test_vc(10), test_vc(11)]);
    assert_eq!(deduped.len(), 2);
}

#[test]
fn dedupe_exact_vcs_preserves_contract_routing_metadata() {
    let plain = test_vc(10);
    let mut contracted = plain.clone();
    contracted.contract_metadata = Some(trust_types::ContractMetadata {
        has_requires: true,
        ..trust_types::ContractMetadata::default()
    });

    assert_eq!(
        trust_vcgen::vc_fingerprint(&plain),
        trust_vcgen::vc_fingerprint(&contracted),
        "the compact structural fingerprint intentionally omits routing metadata"
    );
    let deduped = dedupe_exact_vcs(vec![plain, contracted]);
    assert_eq!(
        deduped.len(),
        2,
        "a compact-hash match must not let a non-contract VC stand in for a contract-routed VC"
    );
}

#[test]
fn verification_is_batteries_on_with_one_off_switch() {
    // The old signature took `verify_off: bool`; the switch is now the
    // `-Ztrust-verify` tri-state itself, so `false`/`true` become `On`/`Off`.
    assert!(rustc_session::trust_verification_enabled_by_flags(
        rustc_session::config::TrustVerify::On
    ));
    assert!(!rustc_session::trust_verification_enabled_by_flags(
        rustc_session::config::TrustVerify::Off
    ));
}

#[test]
fn diagnostic_env_flags_accept_only_explicit_truthy_tokens() {
    for value in ["1", "true", "TRUE", " yes ", "on"] {
        assert!(env_flag_value_enabled(value), "{value:?} should enable env flag");
    }
    for value in ["", "0", "false", "no", "off", "enabled"] {
        assert!(!env_flag_value_enabled(value), "{value:?} should not enable env flag");
    }
}

#[test]
fn explicit_crate_roles_define_scope_without_name_heuristics() {
    assert!(TrustCrateRole::Primary.is_cargo_primary());
    assert!(!TrustCrateRole::Unscoped.is_cargo_primary());
}

#[test]
fn integer_type_range_recognizes_both_comparison_orientations() {
    use trust_types::{Formula as F, Sort};

    let var = || F::Var("x".to_string(), Sort::Int);
    let canonical = F::And(vec![
        F::Ge(Box::new(var()), Box::new(F::Int(-128))),
        F::Le(Box::new(var()), Box::new(F::Int(127))),
    ]);
    let reversed = F::And(vec![
        F::Le(Box::new(F::Int(-128)), Box::new(var())),
        F::Ge(Box::new(F::Int(127)), Box::new(var())),
    ]);

    assert!(is_always_true_type_range(&canonical));
    assert!(is_always_true_type_range(&reversed));

    let not_a_type_range = F::And(vec![
        F::Le(Box::new(F::Int(-127)), Box::new(var())),
        F::Ge(Box::new(F::Int(127)), Box::new(var())),
    ]);
    assert!(!is_always_true_type_range(&not_a_type_range));
}

#[test]
fn batteries_on_policy_is_strict_unless_explicitly_advisory() {
    let strict_policy = test_policy(false, false);
    assert!(!strict_policy.include_dependencies);
    assert!(!strict_policy.includes_non_local_mir());
    assert!(strict_policy.fail_closed());
    assert!(
        !strict_policy
            .skip_is_full_verification_failure(&TrustVerifySkipReason::ExternalDependencyScope)
    );
    assert!(!strict_policy.skip_is_full_verification_failure(&TrustVerifySkipReason::NonLocalMir));
    assert!(strict_policy.skip_is_full_verification_failure(
        &TrustVerifySkipReason::TreatedAsAssumption(
            trust_mir_extract::supportability::UnsupportedReason::PatternType
        )
    ));
    assert!(
        strict_policy.skip_is_full_verification_failure(&TrustVerifySkipReason::UserOptOut),
        "#[trust::skip] cannot silently shrink a strict proof inventory"
    );
    assert!(strict_policy.includes_native_trust_ir_callee_closure());

    let full_dependency_policy = test_policy(false, true);
    assert!(full_dependency_policy.include_dependencies);
    assert!(full_dependency_policy.includes_non_local_mir());
    assert!(
        full_dependency_policy
            .skip_is_full_verification_failure(&TrustVerifySkipReason::ExternalDependencyScope)
    );
    assert!(
        full_dependency_policy
            .skip_is_full_verification_failure(&TrustVerifySkipReason::NonLocalMir)
    );
}

#[test]
fn survey_keeps_batteries_on_verification_nonfatal() {
    let survey_policy = test_policy(true, false);
    assert!(survey_policy.includes_native_trust_ir_callee_closure());
    assert!(survey_policy.is_explicit_advisory());
    assert!(!survey_policy.fail_closed(), "survey must never fail-close");
    assert!(survey_policy.is_explicit_advisory());
    assert!(survey_policy.admits_contract_panic_conditional_evidence());

    let strict_policy = test_policy(false, false);
    assert!(strict_policy.fail_closed());
    assert!(!strict_policy.is_explicit_advisory());
    assert!(!strict_policy.is_explicit_advisory());
    assert!(!strict_policy.admits_contract_panic_conditional_evidence());
}

#[test]
fn whole_crate_coverage_shortfall_is_exact_and_policy_gated() {
    let strict = test_policy(false, false);
    assert!(whole_crate_coverage_shortfall_is_fatal(&strict, 1, 0));
    assert!(whole_crate_coverage_shortfall_is_fatal(&strict, usize::MAX, usize::MAX - 1));
    assert!(whole_crate_coverage_shortfall_is_fatal(&strict, 1, 2));
    assert!(!whole_crate_coverage_shortfall_is_fatal(&strict, usize::MAX, usize::MAX));
    assert!(!whole_crate_coverage_shortfall_is_fatal(&strict, 0, 0));

    // Memory-safe retains this same fail-closed policy object; only the broad
    // advisory policy may report a coverage gap nonfatally.
    let survey = test_policy(true, false);
    assert!(!whole_crate_coverage_shortfall_is_fatal(&survey, 1, 0));
}

#[test]
fn dependency_scope_toggle_is_behavioral() {
    let default_policy = test_policy(false, false);
    let dependency_policy = test_policy(false, true);

    assert!(should_skip_non_local_mir_for_policy(false, &default_policy));
    assert!(!should_skip_non_local_mir_for_policy(false, &dependency_policy));
}

#[test]
fn full_skip_failure_matrix_handles_dependency_and_dead_contract_scopes() {
    let full_policy = test_policy(false, false);
    let full_dependency_policy = test_policy(false, true);

    for reason in
        [TrustVerifySkipReason::ExternalDependencyScope, TrustVerifySkipReason::NonLocalMir]
    {
        assert!(
            !full_policy.skip_is_full_verification_failure(&reason),
            "{reason:?} should be a default-full dependency-scope exemption"
        );
        assert!(
            full_dependency_policy.skip_is_full_verification_failure(&reason),
            "{reason:?} should fail closed when dependency verification is requested"
        );
    }

    for reason in [TrustVerifySkipReason::UnreachableStart, TrustVerifySkipReason::UserOptOut] {
        assert!(
            full_policy.skip_is_full_verification_failure(&reason),
            "{reason:?} should fail closed in explicit full mode"
        );
        assert!(
            full_dependency_policy.skip_is_full_verification_failure(&reason),
            "{reason:?} should fail closed in full dependency mode"
        );
    }

    // `ContractGeneratedClosure`: inherited rustc checker closures are never
    // Trust proof inventory. Trust-active compilations reject the legacy runtime
    // projection, while the vanilla-compatibility lane disables Trust verification.
    // Their absence from the proven set is not a coverage gap; treating it as one
    // either aborted every contract-bearing crate or verified the closure standalone
    // WITHOUT the parent's
    // `#[requires]` over its captures — minting false REFUTATIONS
    // of e.g. the `x + 1` in `ensures(move |ret| *ret == x + 1)` under
    // `requires(x < 100)` (P0: a false refutation of provably-safe Rust).
    assert!(
        !full_policy
            .skip_is_full_verification_failure(&TrustVerifySkipReason::ContractGeneratedClosure),
        "ContractGeneratedClosure (inherited compatibility machinery) is never a gap"
    );
    assert!(
        !full_dependency_policy
            .skip_is_full_verification_failure(&TrustVerifySkipReason::ContractGeneratedClosure),
        "ContractGeneratedClosure is never a gap even with dependency verification requested"
    );

    for policy in [&full_policy, &full_dependency_policy] {
        assert!(
            !policy.skip_is_full_verification_failure(&TrustVerifySkipReason::AssumedTotal),
            "AssumedTotal is a recorded assumption, never a full-verification skip failure"
        );
    }
    assert!(skip_reason_is_recorded_assumption(&TrustVerifySkipReason::AssumedTotal));
    assert_eq!(skip_assumption_tag(&TrustVerifySkipReason::AssumedTotal), "assumed-total");
}

#[test]
fn verification_semantics_key_changes_with_policy_and_level() {
    let default_policy = test_policy(false, false);
    let mut all_policy = default_policy;
    all_policy.include_dependencies = true;

    let solver = "ay:/bin/ay";
    let default_key = verification_semantics_key_from_parts(
        &default_policy,
        1,
        true,
        solver,
        true,
        "aarch64-test;ptr64",
    );
    let all_key = verification_semantics_key_from_parts(
        &all_policy,
        1,
        true,
        solver,
        true,
        "aarch64-test;ptr64",
    );
    let level2_key = verification_semantics_key_from_parts(
        &default_policy,
        2,
        true,
        solver,
        true,
        "aarch64-test;ptr64",
    );

    assert_ne!(default_key, all_key);
    assert_ne!(default_key, level2_key);
}

#[test]
fn vc_artifact_observed_hit_still_generates_fresh_vcs_and_verdicts_for_exact_context() {
    let fresh_calls = std::cell::Cell::new(0usize);
    let generate_for_context = |line: u32, context: &str| {
        // Force the same apparent observation hit for both exact contexts. The
        // observation contains only a count and must not supply either row.
        vc_artifact_observation_then_generate_fresh(Some(17), || {
            fresh_calls.set(fresh_calls.get() + 1);
            let vc = test_vc(line);
            let verdict = VerificationResult::Unknown {
                solver: trust_types::Symbol::intern("fresh-context-probe"),
                time_ms: 0,
                reason: context.to_string(),
            };
            (vec![vc.clone()], vec![(vc, verdict)])
        })
    };

    let first = generate_for_context(41, "exact-context-a");
    let second = generate_for_context(42, "exact-context-b");

    assert_eq!(fresh_calls.get(), 2, "every observed hit must invoke fresh generation");
    assert_eq!(first.0[0].location.line_start, 41);
    assert_eq!(second.0[0].location.line_start, 42);
    assert!(matches!(
        &first.1[0].1,
        VerificationResult::Unknown { reason, .. } if reason == "exact-context-a"
    ));
    assert!(matches!(
        &second.1[0].1,
        VerificationResult::Unknown { reason, .. } if reason == "exact-context-b"
    ));
}

// Trust (cache-key soundness — crate-type/whole-program dependence): the
// whole-program bit MUST perturb the verification-semantics key. A function
// proved `Verified` under a whole-program assumption (e.g. dyn-dispatch trait
// sealedness) is only sound for a closed-world artifact; serving that verdict
// into a downstream-extensible (`rlib`) compilation is a false PROVE. The key
// must therefore differ between `whole_program = true` and `false`, so no cache
// keyed on it can produce a cross hit.
#[test]
fn verification_semantics_key_changes_with_whole_program() {
    let policy = test_policy(false, false);
    let solver = "ay:/bin/ay";

    let whole_program_key =
        verification_semantics_key_from_parts(&policy, 1, true, solver, true, "aarch64-test;ptr64");
    let rlib_key = verification_semantics_key_from_parts(
        &policy,
        1,
        true,
        solver,
        false,
        "aarch64-test;ptr64",
    );

    assert_ne!(
        whole_program_key, rlib_key,
        "whole_program=true (bin/staticlib/cdylib) must not share a cache key with \
         whole_program=false (rlib): a Sealed dyn-dispatch proof valid for a \
         whole-program artifact must not be replayed for a downstream-extensible one"
    );
}

// Trust (target soundness): proofs are target-specific — pointer-width overflow
// obligations and `cfg(target_*)` MIR differ across targets — so the semantics key
// MUST differ between targets, else a cross-compile cache HIT would serve a proof
// computed for a different pointer width as a pass (a false PROVE).
#[test]
fn verification_semantics_key_changes_with_target() {
    let policy = test_policy(false, false);
    let solver = "ay:/bin/ay";
    let key_64 = verification_semantics_key_from_parts(
        &policy,
        1,
        true,
        solver,
        true,
        "aarch64-apple-darwin;ptr64",
    );
    let key_32 = verification_semantics_key_from_parts(
        &policy,
        1,
        true,
        solver,
        true,
        "i686-unknown-linux-gnu;ptr32",
    );
    assert_ne!(
        key_64, key_32,
        "different targets / pointer widths must not share a cache key: a proof \
         computed for one target must never be replayed as a pass for another"
    );
}

#[test]
fn include_dependencies_policy_does_not_alias_default_normal_cache_keys() {
    let default_policy = test_policy(false, false);
    let dependency_policy = TrustVerifyPolicy { include_dependencies: true, ..default_policy };

    let solver = "ay:/bin/ay";
    let default_semantics_key = verification_semantics_key_from_parts(
        &default_policy,
        1,
        true,
        solver,
        true,
        "aarch64-test;ptr64",
    );
    let dependency_semantics_key = verification_semantics_key_from_parts(
        &dependency_policy,
        1,
        true,
        solver,
        true,
        "aarch64-test;ptr64",
    );

    assert_ne!(default_semantics_key, dependency_semantics_key);
    assert_ne!(
        artifact_cache_policy_key(&default_policy),
        artifact_cache_policy_key(&dependency_policy)
    );
}

#[test]
fn batteries_on_dependency_scope_includes_native_trust_ir_callee_closure() {
    let dependency_policy = test_policy(false, true);
    let strict_policy = test_policy(false, false);

    assert!(dependency_policy.includes_non_local_mir());
    assert!(dependency_policy.includes_native_trust_ir_callee_closure());
    assert!(strict_policy.includes_native_trust_ir_callee_closure());
}

#[derive(Clone)]
struct NativeTrustIrUnitEngine {
    manifest: trust_verifier_api::EngineManifest,
    supported_kind: trust_verifier_api::ObligationKind,
    proof_strength: trust_verifier_api::ProofStrength,
    artifacts: Vec<trust_verifier_api::EvidenceArtifact>,
    calls: std::sync::Arc<std::sync::Mutex<Vec<String>>>,
}

impl NativeTrustIrUnitEngine {
    fn new(
        name: &str,
        engine_kind: trust_verifier_api::EngineKind,
        supported_kind: trust_verifier_api::ObligationKind,
        proof_strength: trust_verifier_api::ProofStrength,
        artifacts: Vec<trust_verifier_api::EvidenceArtifact>,
        calls: std::sync::Arc<std::sync::Mutex<Vec<String>>>,
    ) -> Self {
        let mut manifest =
            trust_verifier_api::EngineManifest::new(name, "native-trust-ir-test", engine_kind);
        if name == "trust-vc" {
            manifest.repository = Some("trust-vc-bridge".to_string());
        }
        manifest.capabilities.push(trust_verifier_api::EngineCapability {
            obligation_kind: supported_kind.clone(),
            support: trust_verifier_api::SupportLevel::Preferred,
        });
        Self { manifest, supported_kind, proof_strength, artifacts, calls }
    }
}

impl trust_verifier_api::VerificationEngine for NativeTrustIrUnitEngine {
    fn manifest(&self) -> &trust_verifier_api::EngineManifest {
        &self.manifest
    }

    fn supports(
        &self,
        obligation: &trust_verifier_api::TrustObligation,
    ) -> trust_verifier_api::SupportLevel {
        if obligation.kind == self.supported_kind {
            trust_verifier_api::SupportLevel::Preferred
        } else {
            trust_verifier_api::SupportLevel::Unsupported {
                reason: format!("{} only handles {:?}", self.manifest.name, self.supported_kind),
            }
        }
    }

    fn verify_validated(
        &self,
        request: trust_verifier_api::ValidatedVerificationRequest<'_>,
    ) -> Vec<trust_verifier_api::ObligationEvidence> {
        let obligations = request.obligations();
        self.calls.lock().expect("native test engine calls lock").push(self.manifest.name.clone());
        obligations
            .iter()
            .filter(|obligation| obligation.kind == self.supported_kind)
            .map(|obligation| trust_verifier_api::ObligationEvidence {
                evidence_id: format!("{}:{}", self.manifest.name, obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: trust_verifier_api::EvidenceStatus::Proved,
                proof_strength: Some(self.proof_strength.clone()),
                artifacts: materialize_native_unit_test_artifacts(
                    &self.manifest.name,
                    obligation,
                    &self.artifacts,
                ),
                counterexample: None,
                publication: trust_verifier_api::EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            })
            .collect()
    }
}

/// Build the exact owner-bound proof DAG required by the public verifier API.
///
/// These unit engines deliberately start from lightweight artifact templates so
/// tests can select a proof family without hard-coding digests. Materialize
/// those templates per obligation: reusing one fixed envelope across owners
/// would itself be an invalid proof transplant and would make the native-route
/// tests exercise the rejection path instead of the intended accepted path.
fn exact_native_unit_test_proof_dag(
    owner: &str,
    engine_name: &str,
    seed: &str,
) -> Vec<trust_verifier_api::EvidenceArtifact> {
    use trust_verifier_api::{
        EvidenceArtifact, EvidenceArtifactKind, EvidenceArtifactMaterialization,
        EvidenceArtifactReference,
    };

    let binding = owner;
    let (input_materialization, input_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::NormalizedObligation,
        format!("native unit normalized input:{seed}").as_bytes(),
        binding,
        owner,
        Vec::new(),
    )
    .expect("bounded native-unit normalized input");
    let input = EvidenceArtifact {
        kind: EvidenceArtifactKind::NormalizedObligation,
        uri: format!("artifact://trustc-native-unit/normalized/{}", input_hash.value),
        hash: input_hash,
        materialization: Some(input_materialization),
    };
    let (transcript_materialization, transcript_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::SolverTranscript,
        format!("native unit transcript:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference { kind: input.kind, hash: input.hash.clone() }],
    )
    .expect("bounded native-unit transcript");
    let transcript = EvidenceArtifact {
        kind: EvidenceArtifactKind::SolverTranscript,
        uri: format!("artifact://trustc-native-unit/transcript/{}", transcript_hash.value),
        hash: transcript_hash,
        materialization: Some(transcript_materialization),
    };

    let mut artifacts = vec![input, transcript.clone()];
    let check_parent = if engine_name == "trust-mc" {
        let (replay_materialization, replay_hash) = EvidenceArtifactMaterialization::new_bound(
            EvidenceArtifactKind::ReplayLog,
            format!("native unit replay:{seed}").as_bytes(),
            binding,
            owner,
            vec![EvidenceArtifactReference {
                kind: transcript.kind,
                hash: transcript.hash.clone(),
            }],
        )
        .expect("bounded native-unit replay");
        let replay = EvidenceArtifact {
            kind: EvidenceArtifactKind::ReplayLog,
            uri: format!("artifact://trustc-native-unit/replay/{}", replay_hash.value),
            hash: replay_hash,
            materialization: Some(replay_materialization),
        };
        artifacts.push(replay.clone());
        replay
    } else {
        transcript
    };
    let (check_materialization, check_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCheckReport,
        format!("native unit check:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference {
            kind: check_parent.kind,
            hash: check_parent.hash.clone(),
        }],
    )
    .expect("bounded native-unit check");
    artifacts.push(EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCheckReport,
        uri: format!("artifact://trustc-native-unit/check/{}", check_hash.value),
        hash: check_hash,
        materialization: Some(check_materialization),
    });
    artifacts
}

fn materialize_native_unit_test_artifacts(
    engine_name: &str,
    obligation: &trust_verifier_api::TrustObligation,
    templates: &[trust_verifier_api::EvidenceArtifact],
) -> Vec<trust_verifier_api::EvidenceArtifact> {
    let certificates = templates
        .iter()
        .filter(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::ProofCertificate
        })
        .count();
    if certificates == 1 && templates.len() == 1 {
        let seed = &templates[0].uri;
        let owner = obligation.obligation_id.as_str();
        let (materialization, hash) =
            trust_verifier_api::EvidenceArtifactMaterialization::new_bound(
                trust_verifier_api::EvidenceArtifactKind::ProofCertificate,
                format!("native unit certificate:{seed}").as_bytes(),
                owner,
                owner,
                Vec::new(),
            )
            .expect("bounded native-unit certificate");
        return vec![trust_verifier_api::EvidenceArtifact {
            kind: trust_verifier_api::EvidenceArtifactKind::ProofCertificate,
            uri: format!("artifact://trustc-native-unit/certificate/{}", hash.value),
            hash,
            materialization: Some(materialization),
        }];
    }
    let has_transcript = templates.iter().any(|artifact| {
        artifact.kind == trust_verifier_api::EvidenceArtifactKind::SolverTranscript
    });
    let has_consumer = templates.iter().any(|artifact| {
        matches!(
            artifact.kind,
            trust_verifier_api::EvidenceArtifactKind::ProofCheckReport
                | trust_verifier_api::EvidenceArtifactKind::ProofReplayTrace
                | trust_verifier_api::EvidenceArtifactKind::ReplayLog
        )
    });
    if has_transcript && has_consumer {
        let seed =
            templates.iter().map(|artifact| artifact.uri.as_str()).collect::<Vec<_>>().join("|");
        exact_native_unit_test_proof_dag(&obligation.obligation_id, engine_name, &seed)
    } else {
        templates.to_vec()
    }
}

fn native_trust_ir_test_artifact(
    kind: trust_verifier_api::EvidenceArtifactKind,
    label: &str,
) -> trust_verifier_api::EvidenceArtifact {
    trust_verifier_api::EvidenceArtifact {
        kind,
        uri: format!("artifact://native-trust-ir-test/{label}"),
        hash: trust_verifier_api::ArtifactHash {
            algorithm: "sha256".to_string(),
            value: trust_types::stable_sha256_hex(label.as_bytes()),
        },
        materialization: None,
    }
}

fn trust_vc_native_trust_ir_test_proof_certificate_artifact(
    label: &str,
) -> trust_verifier_api::EvidenceArtifact {
    let digest = trust_types::stable_sha256_hex(label.as_bytes());
    trust_verifier_api::EvidenceArtifact {
        kind: trust_verifier_api::EvidenceArtifactKind::ProofCertificate,
        uri: format!("artifact://trust-vc/native-trust-ir-proof-artifacts/{digest}.json"),
        hash: trust_verifier_api::ArtifactHash { algorithm: "sha256".to_string(), value: digest },
        materialization: None,
    }
}

fn test_api_evidence(
    proof_strength: trust_verifier_api::ProofStrength,
    artifacts: Vec<trust_verifier_api::EvidenceArtifact>,
) -> trust_verifier_api::ObligationEvidence {
    trust_verifier_api::ObligationEvidence {
        evidence_id: "test-evidence".to_string(),
        obligation_id: "test-obligation".to_string(),
        engine: trust_verifier_api::EngineManifest::new(
            "test-engine",
            "0.0.0",
            trust_verifier_api::EngineKind::Composite,
        ),
        status: trust_verifier_api::EvidenceStatus::Proved,
        proof_strength: Some(proof_strength),
        artifacts,
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: Vec::new(),
    }
}

#[test]
fn native_api_proved_without_artifact_policy_is_legacy_unknown() {
    let evidence = test_api_evidence(trust_verifier_api::ProofStrength::smt_unsat(), Vec::new());

    let result = legacy_result_from_api_evidence(&evidence);

    assert!(
        matches!(result, VerificationResult::Unknown { ref reason, .. } if reason.contains("lacks required artifacts")),
        "weak native API proof evidence must not become legacy Proved: {result:?}"
    );
}

#[test]
fn transport_proof_status_requires_unbounded_artifact_backed_evidence() {
    let weak = test_api_evidence(trust_verifier_api::ProofStrength::smt_unsat(), Vec::new());
    assert_eq!(transport_proof_status(&weak), TransportProofStatus::Unknown);

    let strong = test_api_evidence(
        trust_verifier_api::ProofStrength::smt_unsat(),
        exact_native_unit_test_proof_dag("test-obligation", "test-engine", "transport-status"),
    );
    assert_eq!(transport_proof_status(&strong), TransportProofStatus::Proved);
}

#[test]
fn compiler_trust_status_requires_complete_sound_proof_strength() {
    assert!(proof_strength_satisfies_static_trust(&ProofStrength::smt_unsat()));
    assert!(!proof_strength_satisfies_static_trust(&ProofStrength::bounded(8)));
    assert!(!proof_strength_satisfies_static_trust(&ProofStrength {
        reasoning: trust_types::ReasoningKind::Smt,
        assurance: trust_types::AssuranceLevel::Heuristic,
    }));
}

fn native_trust_ir_test_span(line_start: u32) -> trust_types::SourceSpan {
    trust_types::SourceSpan {
        file: "src/lib.rs".to_string(),
        line_start,
        col_start: 1,
        line_end: line_start,
        col_end: 20,
    }
}

fn native_trust_ir_test_source_location(line_start: u32) -> trust_verifier_api::SourceLocation {
    trust_verifier_api::SourceLocation {
        file: Some("src/lib.rs".to_string()),
        line: Some(line_start),
        column: Some(1),
        end_line: Some(line_start),
        end_column: Some(20),
        ..trust_verifier_api::SourceLocation::default()
    }
}

fn test_obligation_metadata<'a>(
    obligation: &'a trust_verifier_api::TrustObligation,
    key: &str,
) -> &'a str {
    obligation
        .metadata
        .iter()
        .find(|entry| entry.key == key)
        .map(|entry| entry.value.as_str())
        .unwrap_or_else(|| panic!("missing obligation metadata key `{key}`"))
}

fn mutate_test_obligation_context(
    obligation: &mut trust_verifier_api::TrustObligation,
    mutate: impl FnOnce(&mut trust_verifier_api::ObligationContext),
) {
    let position = obligation
        .metadata
        .iter()
        .position(|entry| {
            matches!(trust_verifier_api::ObligationContext::from_metadata_entry(entry), Ok(Some(_)))
        })
        .expect("test obligation context");
    let mut context =
        trust_verifier_api::ObligationContext::from_metadata_entry(&obligation.metadata[position])
            .expect("parse test obligation context")
            .expect("test obligation context entry");
    mutate(&mut context);
    obligation.metadata[position] =
        context.to_metadata_entry().expect("serialize mutated test obligation context");
}

fn test_obligation_metadata_json(
    obligation: &trust_verifier_api::TrustObligation,
    key: &str,
) -> serde_json::Value {
    serde_json::from_str(test_obligation_metadata(obligation, key))
        .unwrap_or_else(|error| panic!("invalid JSON metadata `{key}`: {error}"))
}

fn assert_native_proof_unit_metadata(
    obligation: &trust_verifier_api::TrustObligation,
    suite: &str,
) -> serde_json::Value {
    for key in [
        super::TRUST_TRUST_IR_NATIVE_PROOF_UNIT_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY,
        super::TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY,
    ] {
        assert!(
            obligation.metadata.iter().any(|entry| entry.key == key),
            "{suite} obligation must carry first-class native TrustIr proof-unit metadata `{key}`"
        );
    }
    let proof_unit = test_obligation_metadata_json(
        obligation,
        super::TRUST_TRUST_IR_NATIVE_PROOF_UNIT_METADATA_KEY,
    );
    let request_id = test_obligation_metadata(
        obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    );
    let proof_id = test_obligation_metadata(
        obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    );
    assert_eq!(proof_unit["schema_version"], super::TRUST_TRUST_IR_NATIVE_PROOF_UNIT_SCHEMA);
    assert_eq!(proof_unit["verifier_suite"], suite);
    let expected_native_id =
        format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
    assert_eq!(proof_unit["native_id"].as_str(), Some(expected_native_id.as_str()));
    assert_eq!(
        proof_unit["public_obligation_id"].as_str(),
        Some(obligation.obligation_id.as_str()),
        "{suite} proof unit must bind the exact public verifier obligation"
    );
    assert_eq!(
        proof_unit["obligation_source"]["public_obligation_id"].as_str(),
        Some(obligation.obligation_id.as_str()),
        "{suite} compiler-fact source must mirror the typed public binding"
    );
    assert_eq!(proof_unit["proof_status"], "pending_native_evidence");
    assert_eq!(
        proof_unit["trust_ir_module_digest"]["value"].as_str(),
        Some(test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY,
        ))
    );
    assert_eq!(
        proof_unit["compiler_facts_digest"]["value"].as_str(),
        Some(test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY,
        ))
    );
    assert_eq!(
        proof_unit["obligation_source_digest"]["value"].as_str(),
        Some(test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY,
        ))
    );
    assert_eq!(
        proof_unit["artifact_fingerprint"]["value"].as_str(),
        Some(test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY,
        ))
    );
    assert!(
        proof_unit["obligation_source"]["assertion_id"].as_u64().is_some(),
        "{suite} native proof-unit metadata should bind the compiler assertion id"
    );
    proof_unit
}

#[test]
fn trust_mc_compiler_transport_rows_share_canonical_native_identity() {
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo::f:arithmetic:0".to_string(),
        kind: trust_verifier_api::ObligationKind::ArithmeticSafety,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "arithmetic safety".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                    .to_string(),
                value: "trust-mc".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                    .to_string(),
                value: "7".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
                    .to_string(),
                value: "42".to_string(),
            },
        ],
    };
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-trust-mc-transport",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::f".to_string(),
        },
    );
    bundle.obligations.push(obligation.clone());
    let evidence = trust_verifier_api::ObligationEvidence {
        evidence_id: "trust-mc-proof-42".to_string(),
        obligation_id: obligation.obligation_id.clone(),
        engine: trust_verifier_api::EngineManifest::new(
            "trust-mc",
            "native-trust-ir-test",
            trust_verifier_api::EngineKind::Reachability,
        ),
        status: trust_verifier_api::EvidenceStatus::Proved,
        proof_strength: Some(trust_verifier_api::ProofStrength {
            reasoning: trust_verifier_api::ReasoningKind::Pdr,
            assurance: trust_verifier_api::AssuranceLevel::SmtBacked,
        }),
        artifacts: vec![
            trust_verifier_api::EvidenceArtifact {
                kind: trust_verifier_api::EvidenceArtifactKind::EngineInput,
                uri: "trust_ir-native://verification-bundle/demo/trust-mc/request/7".to_string(),
                hash: trust_verifier_api::ArtifactHash {
                    algorithm: "sha256".to_string(),
                    value: trust_types::stable_sha256_hex(b"trust-mc-request-7"),
                },
                materialization: None,
            },
            trust_verifier_api::EvidenceArtifact {
                kind: trust_verifier_api::EvidenceArtifactKind::NormalizedObligation,
                uri: "trust_ir-native://verification-bundle/demo/trust-mc/request/7/proof/42"
                    .to_string(),
                hash: trust_verifier_api::ArtifactHash {
                    algorithm: "sha256".to_string(),
                    value: trust_types::stable_sha256_hex(b"trust-mc-proof-42"),
                },
                materialization: None,
            },
            native_trust_ir_test_artifact(
                trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                "trust-mc-solver-transcript",
            ),
            native_trust_ir_test_artifact(
                trust_verifier_api::EvidenceArtifactKind::ProofCheckReport,
                "trust-mc-proof-check",
            ),
        ],
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: Vec::new(),
    };
    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("trust-mc-transport-test").snapshot(),
        &bundle,
        evidence.engine.clone(),
        &[obligation.clone()],
        vec![evidence.clone()],
    );

    let native =
        transport_native_trust_ir_evidence(&obligation, Some(&evidence), None, &full_result)
            .expect("trust-mc native TrustIr transport evidence should be present");
    let proof = transport_proof_evidence(&obligation, Some(&evidence), None, &full_result)
        .expect("trust-mc proof transport evidence should be present");

    assert_eq!(native.suite, "trust-mc");
    assert_eq!(proof.suite, "trust-mc");
    assert_eq!(native.request_id.as_deref(), Some("7"));
    assert_eq!(proof.request_id.as_deref(), native.request_id.as_deref());
    assert_eq!(native.native_id.as_deref(), Some("trust_ir-native-trust-mc-request-7-proof-42"));
    assert_eq!(proof.native_id.as_deref(), native.native_id.as_deref());
}

#[test]
fn native_transport_identity_uses_canonical_native_proof_unit_ids_for_native_suites() {
    for (suite, expected) in [
        ("trust-vc", "trust_ir-native-trust-vc-request-3-proof-11"),
        ("trust-wp", "trust_ir-native-trust-wp-request-3-proof-11"),
        ("trust-mc", "trust_ir-native-trust-mc-request-3-proof-11"),
    ] {
        let obligation = trust_verifier_api::TrustObligation {
            obligation_id: format!("vc:demo:{suite}:0"),
            kind: trust_verifier_api::ObligationKind::Assertion,
            contract_id: None,
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation::default(),
            description: "native proof unit identity".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: vec![
                trust_verifier_api::MetadataEntry {
                    key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                        .to_string(),
                    value: suite.to_string(),
                },
                trust_verifier_api::MetadataEntry {
                    key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                        .to_string(),
                    value: "3".to_string(),
                },
                trust_verifier_api::MetadataEntry {
                    key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
                        .to_string(),
                    value: "11".to_string(),
                },
            ],
        };

        assert_eq!(native_transport_identity(&obligation).native_id.as_deref(), Some(expected));
    }
}

fn native_trust_ir_compiler_function() -> (
    trust_types::VerifiableFunction,
    trust_types::CompilerContractBundle,
    Vec<VerificationCondition>,
) {
    let contract = trust_types::Contract {
        kind: trust_types::ContractKind::Ensures,
        span: native_trust_ir_test_span(7),
        body: "true".to_string(),
    };
    let function = trust_types::VerifiableFunction {
        name: "checked_transfer".to_string(),
        def_path: "demo::checked_transfer".to_string(),
        span: native_trust_ir_test_span(6),
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Bool,
                    name: Some("_0".to_string()),
                },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Ref {
                        mutable: false,
                        inner: Box::new(trust_types::Ty::Int { width: 32, signed: false }),
                    },
                    name: Some("account".to_string()),
                },
            ],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: Vec::new(),
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 1,
            return_ty: trust_types::Ty::Bool,
        },
        contracts: vec![contract.clone()],
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    };
    let compiler_contracts = trust_types::CompilerContractBundle::new(vec![contract]);
    let vcs = vec![
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
            },
            function: trust_types::Symbol::intern("demo::checked_transfer"),
            location: native_trust_ir_test_span(10),
            formula: trust_types::Formula::And(vec![
                trust_types::Formula::Ge(
                    Box::new(trust_types::Formula::Var(
                        "amount".to_string(),
                        trust_types::Sort::Int,
                    )),
                    Box::new(trust_types::Formula::Int(0)),
                ),
                trust_types::Formula::Lt(
                    Box::new(trust_types::Formula::Var(
                        "amount".to_string(),
                        trust_types::Sort::Int,
                    )),
                    Box::new(trust_types::Formula::Int(0)),
                ),
            ]),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::checked_transfer"),
            location: native_trust_ir_test_span(11),
            // Keep the ownership context (the reference local + AliasingViolation
            // kind), but use the bridge's proven release-admissible QF_LIA shape.
            // The old BV reflexivity contradiction was replayable but required a
            // non-kernel theory step, so it correctly stopped minting a live receipt
            // once the bridge began requiring full TrustVC release admission.
            formula: trust_types::Formula::And(vec![
                trust_types::Formula::Lt(
                    Box::new(trust_types::Formula::Var(
                        "amount".to_string(),
                        trust_types::Sort::Int,
                    )),
                    Box::new(trust_types::Formula::Int(16)),
                ),
                trust_types::Formula::Ge(
                    Box::new(trust_types::Formula::Var(
                        "amount".to_string(),
                        trust_types::Sort::Int,
                    )),
                    Box::new(trust_types::Formula::Int(16)),
                ),
            ]),
            contract_metadata: None,
        },
    ];

    (function, compiler_contracts, vcs)
}

fn fresh_nonlegacy_vc_binding_fixture() -> (
    trust_types::VerifiableFunction,
    Vec<VerificationCondition>,
    trust_verifier_api::TrustContractBundle,
) {
    let (function, compiler_contracts, _) = native_trust_ir_compiler_function();
    let vcs = vec![VerificationCondition {
        // Bounds checks are TrustVC-owned and therefore carry the separate
        // MIR-memory proof unit whose exact public semantics must be sealed by
        // the fresh-VC re-key identity.
        kind: VcKind::IndexOutOfBounds,
        function: trust_types::Symbol::intern(&function.name),
        location: native_trust_ir_test_span(29),
        // The public typed formula carrier and the legacy decoder both support
        // bitvectors. Fresh-VC authority is nevertheless independently gated
        // below by exact context, location, digest, schema, and multiplicity.
        formula: Formula::Eq(
            Box::new(Formula::Var("n".to_string(), Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
        ),
        contract_metadata: None,
    }];
    let bundle =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
    (function, vcs, bundle)
}

fn fresh_rekey_tampered_summary_fact() -> trust_verifier_api::SummaryFact {
    trust_verifier_api::SummaryFact::new(
        "tampered-fact",
        "tampered-test-producer",
        "tampered-test-crate",
        "tampered_test::item",
        trust_verifier_api::SummaryFactKind::PointerProvenanceEq {
            left: "p".to_string(),
            right: "q".to_string(),
        },
        trust_verifier_api::ArtifactHash {
            algorithm: "sha256".to_string(),
            value: "00".repeat(32),
        },
    )
}

fn single_fresh_vc_binding_fixture(
    kind: VcKind,
    formula: Formula,
    line: u32,
) -> (
    trust_types::VerifiableFunction,
    Vec<VerificationCondition>,
    trust_verifier_api::TrustContractBundle,
) {
    let (function, compiler_contracts, _) = native_trust_ir_compiler_function();
    let vcs = vec![VerificationCondition {
        kind,
        function: trust_types::Symbol::intern(&function.name),
        location: native_trust_ir_test_span(line),
        formula,
        contract_metadata: None,
    }];
    let bundle =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
    (function, vcs, bundle)
}

fn exact_fresh_test_obligation<'a>(
    function: &trust_types::VerifiableFunction,
    vcs: &[VerificationCondition],
    bundle: &'a trust_verifier_api::TrustContractBundle,
) -> &'a trust_verifier_api::TrustObligation {
    bundle
        .obligations
        .iter()
        .find(|obligation| {
            exact_fresh_vc_index_for_obligation_without_multiplicity(function, obligation, vcs)
                == Some(0)
        })
        .expect("exact fresh VC obligation")
}

fn assert_fresh_metadata_key_is_sealed(
    function: &trust_types::VerifiableFunction,
    vcs: &[VerificationCondition],
    obligation: &trust_verifier_api::TrustObligation,
    key: &str,
) {
    let matching = obligation.metadata.iter().filter(|entry| entry.key == key).count();
    assert_eq!(matching, 1, "fixture must contain exactly one `{key}` entry");

    let mut removed = obligation.clone();
    removed.metadata.retain(|entry| entry.key != key);
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(function, &removed, vcs),
        None,
        "removing `{key}` must fail closed"
    );

    let mut changed = obligation.clone();
    changed
        .metadata
        .iter_mut()
        .find(|entry| entry.key == key)
        .expect("sealed metadata")
        .value
        .push_str("-tampered");
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(function, &changed, vcs),
        None,
        "changing `{key}` must fail closed"
    );

    let mut duplicated = obligation.clone();
    let duplicate =
        duplicated.metadata.iter().find(|entry| entry.key == key).expect("sealed metadata").clone();
    duplicated.metadata.push(duplicate);
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(function, &duplicated, vcs),
        None,
        "duplicating `{key}` must fail closed"
    );
}

fn fresh_test_run_with_one_strict_proof(
    bundle: &trust_verifier_api::TrustContractBundle,
    proved_obligation_id: &str,
    context: trust_verifier_api::VerifierExecutionSnapshot,
) -> trust_verifier_api::VerificationRunResult {
    let proved_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == proved_obligation_id)
        .expect("proved obligation in bundle")
        .clone();
    let strict = authority_test_strict_native_run(proved_obligation);
    let proved = strict.evidence.into_iter().next().expect("strict proof evidence");
    let engine = proved.engine.clone();
    let mut evidence = bundle
        .obligations
        .iter()
        .map(|obligation| {
            if obligation.obligation_id == proved_obligation_id {
                proved.clone()
            } else {
                unsupported_evidence_for(obligation)
            }
        })
        .collect::<Vec<_>>();
    for row in &mut evidence {
        row.engine = engine.clone();
    }
    trust_verifier_api::VerificationRunResult::from_evidence(
        context,
        bundle,
        engine,
        &bundle.obligations,
        evidence,
    )
}

#[test]
fn fresh_rekey_requires_exact_compiler_crate_instance_and_rejects_replay() {
    const FIRST_STABLE_ID: u64 = 0xaa;
    const SECOND_STABLE_ID: u64 = 0x22;
    let (function, compiler_contracts, vcs) = native_trust_ir_compiler_function();
    let first = trust_mir_extract::function_to_verifier_api_bundle_with_compiler_identity(
        &function,
        &compiler_contracts,
        &vcs,
        "demo",
        FIRST_STABLE_ID,
    );
    let second = trust_mir_extract::function_to_verifier_api_bundle_with_compiler_identity(
        &function,
        &compiler_contracts,
        &vcs,
        "demo",
        SECOND_STABLE_ID,
    );
    let first_authority = CompilerFunctionAuthority::exact(
        trust_verifier_api::FunctionContext {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
        FIRST_STABLE_ID,
    );
    let second_authority = CompilerFunctionAuthority::exact(
        trust_verifier_api::FunctionContext {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
        SECOND_STABLE_ID,
    );
    let first_snapshot = exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
        &function,
        &compiler_contracts,
        &first,
        &first.obligations,
        &vcs,
        ExactDefinitionEntryMarkerSet::default(),
        &first_authority,
        trust_router::VerifierExecutionContext::new("stable-crate-replay-test").snapshot(),
    );
    let second_snapshot = exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
        &function,
        &compiler_contracts,
        &second,
        &second.obligations,
        &vcs,
        ExactDefinitionEntryMarkerSet::default(),
        &second_authority,
        trust_router::VerifierExecutionContext::new("stable-crate-replay-test").snapshot(),
    );
    assert!(first_snapshot.complete);
    assert!(second_snapshot.complete);

    let replay = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("stable-crate-replay-test").snapshot(),
        &first,
        trust_verifier_api::EngineManifest::new(
            "stable-crate-replay-test",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &first.obligations,
        first.obligations.iter().map(unsupported_evidence_for).collect(),
    );
    assert!(!exact_fresh_vc_rekey_run_is_complete(&second, &replay, &vcs, &second_snapshot,));

    for mismatch in [
        "missing-sidecar",
        "duplicate-sidecar",
        "uppercase-sidecar",
        "wrong-sidecar",
        "wrong-bundle-id",
        "joint-other-crate-instance",
    ] {
        let mut bundle = first.clone();
        match mismatch {
            "missing-sidecar" => bundle
                .metadata
                .retain(|entry| entry.key != TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY),
            "duplicate-sidecar" => bundle.metadata.push(trust_verifier_api::MetadataEntry {
                key: TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY.to_string(),
                value: format!("{FIRST_STABLE_ID:016x}"),
            }),
            "uppercase-sidecar" => {
                bundle
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY)
                    .expect("stable crate identity")
                    .value = "00000000000000AA".to_string();
            }
            "wrong-sidecar" => {
                bundle
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY)
                    .expect("stable crate identity")
                    .value = "0000000000000022".to_string();
            }
            "wrong-bundle-id" => bundle.bundle_id.push_str(":forged"),
            "joint-other-crate-instance" => {
                bind_test_compiler_identity(&mut bundle, SECOND_STABLE_ID);
            }
            _ => unreachable!(),
        }
        let snapshot = exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
            &function,
            &compiler_contracts,
            &bundle,
            &bundle.obligations,
            &vcs,
            ExactDefinitionEntryMarkerSet::default(),
            &first_authority,
            trust_router::VerifierExecutionContext::new("stable-crate-replay-test").snapshot(),
        );
        assert!(!snapshot.complete, "mismatch `{mismatch}` must fail closed");
    }
}

#[test]
fn fresh_vc_rekey_requires_exact_context_location_digest_and_schema() {
    let (function, vcs, bundle) = fresh_nonlegacy_vc_binding_fixture();
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            exact_fresh_vc_index_for_obligation_without_multiplicity(&function, obligation, &vcs)
                == Some(0)
        })
        .expect("fresh VC obligation");
    assert_eq!(
        legacy_vc_from_api_obligation(&function, obligation).formula,
        vcs[0].formula,
        "the widened legacy decoder must preserve the exact BV formula; fresh-context authority remains independently gated"
    );
    let source_digest = trust_mir_extract::verifier_source_digest(&function);
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        panic!("function bundle subject")
    };
    let expected_function =
        trust_verifier_api::FunctionContext { crate_name: crate_name.clone(), path: path.clone() };
    let authority = CompilerFunctionAuthority::compatibility_for_test(expected_function);
    let multiplicity =
        exact_fresh_vc_match_multiplicity(&function, &bundle, &vcs, &source_digest, &authority);
    assert_eq!(multiplicity.get(&0), Some(&1));
    assert!(
        exact_unique_fresh_vc_for_obligation(
            &function,
            obligation,
            &vcs,
            &multiplicity,
            &source_digest,
        )
        .is_some_and(|selected| std::ptr::eq(selected, &vcs[0]))
    );

    let mut out_of_range = obligation.clone();
    mutate_test_obligation_context(&mut out_of_range, |context| {
        let trust_verifier_api::ObligationOrigin::VerificationCondition { vc_index, .. } =
            &mut context.origin
        else {
            panic!("VC context")
        };
        *vc_index = vcs.len();
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &out_of_range, &vcs,),
        None
    );

    let mut wrong_location = obligation.clone();
    wrong_location.source.line = Some(999);
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &wrong_location, &vcs,),
        None
    );

    let mut wrong_crate = obligation.clone();
    mutate_test_obligation_context(&mut wrong_crate, |context| {
        context.function.as_mut().expect("VC function context").crate_name.push_str("_tampered");
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &wrong_crate, &vcs,),
        None
    );

    let mut wrong_path = obligation.clone();
    mutate_test_obligation_context(&mut wrong_path, |context| {
        context.function.as_mut().expect("VC function context").path.push_str("::tampered");
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &wrong_path, &vcs),
        None
    );

    let mut wrong_context_schema = obligation.clone();
    mutate_test_obligation_context(&mut wrong_context_schema, |context| {
        context.schema_version.push_str("-tampered");
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(
            &function,
            &wrong_context_schema,
            &vcs,
        ),
        None
    );

    let mut wrong_producer = obligation.clone();
    mutate_test_obligation_context(&mut wrong_producer, |context| {
        context.producer = trust_verifier_api::ObligationProducer::VcGenerator;
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &wrong_producer, &vcs,),
        None
    );

    let mut wrong_vc_kind = obligation.clone();
    mutate_test_obligation_context(&mut wrong_vc_kind, |context| {
        let trust_verifier_api::ObligationOrigin::VerificationCondition { vc_kind, .. } =
            &mut context.origin
        else {
            panic!("VC context")
        };
        vc_kind.push_str("_tampered");
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &wrong_vc_kind, &vcs,),
        None
    );

    for key in [
        TRUST_VC_DIGEST_METADATA_KEY,
        TRUST_VC_FORMULA_SCHEMA_METADATA_KEY,
        TRUST_VC_FORMULA_SORT_METADATA_KEY,
        TRUST_VC_FORMULA_SMTLIB_METADATA_KEY,
        TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY,
        TRUST_SOURCE_DIGEST_METADATA_KEY,
        TRUST_VC_KIND_METADATA_KEY,
        TRUST_VC_CONDITION_ORIGIN_METADATA_KEY,
        TRUST_VC_PROOF_OBLIGATION_METADATA_KEY,
        TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
    ] {
        assert_fresh_metadata_key_is_sealed(&function, &vcs, obligation, key);
    }

    let mut falsely_pruned = obligation.clone();
    falsely_pruned.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_PRUNED_METADATA_KEY.to_string(),
        value: "true".to_string(),
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &falsely_pruned, &vcs,),
        None,
        "adding a pruning claim changes the public formula semantics"
    );

    let mut injected_proof_unit_failure = obligation.clone();
    injected_proof_unit_failure.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY.to_string(),
        value: "tampered unsupported alternative".to_string(),
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(
            &function,
            &injected_proof_unit_failure,
            &vcs,
        ),
        None,
        "a supported TrustVC proof unit cannot acquire an unsupported alternative"
    );

    for mutate in [
        |obligation: &mut trust_verifier_api::TrustObligation| {
            obligation.obligation_id.push_str("-tampered");
        },
        |obligation: &mut trust_verifier_api::TrustObligation| {
            obligation.description.push_str("-tampered");
        },
    ] {
        let mut tampered = obligation.clone();
        mutate(&mut tampered);
        assert_eq!(
            exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &tampered, &vcs,),
            None
        );
    }
    let mut wrong_public_kind = obligation.clone();
    wrong_public_kind.kind = trust_verifier_api::ObligationKind::Assertion;
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(
            &function,
            &wrong_public_kind,
            &vcs,
        ),
        None
    );

    let mut wrong_strength = obligation.clone();
    wrong_strength.required_strength = None;
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &wrong_strength, &vcs,),
        None,
        "the public proof-strength requirement is part of the exact claim"
    );

    let mut injected_proof_item = obligation.clone();
    injected_proof_item.proof_item_id = Some("forged-proof-item".to_string());
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(
            &function,
            &injected_proof_item,
            &vcs,
        ),
        None,
        "a generated compiler VC cannot acquire proof-item authority"
    );

    let mut injected_summary_fact = obligation.clone();
    injected_summary_fact.summary_facts.push(fresh_rekey_tampered_summary_fact());
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(
            &function,
            &injected_summary_fact,
            &vcs,
        ),
        None,
        "an injected trust-wp proof assumption must fail closed"
    );

    let encoded_summary_fact =
        serde_json::to_string(&fresh_rekey_tampered_summary_fact()).expect("summary fact JSON");
    for key in [
        trust_verifier_api::SUMMARY_FACT_METADATA_KEY,
        TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
    ] {
        let mut injected = obligation.clone();
        injected.metadata.push(trust_verifier_api::MetadataEntry {
            key: key.to_string(),
            value: encoded_summary_fact.clone(),
        });
        assert_eq!(
            exact_fresh_vc_index_for_obligation_without_multiplicity(&function, &injected, &vcs,),
            None,
            "an injected `{key}` proof assumption must fail closed"
        );
    }
}

#[test]
fn impl_method_fresh_rekey_binds_exact_compiler_crate_identity() {
    let (mut function, compiler_contracts, _) = native_trust_ir_compiler_function();
    function.name = "rank".to_string();
    function.def_path =
        "<sealed_dyn_probe::Button as sealed_dyn_probe::sealed::Widget>::rank".to_string();
    let vcs = vec![VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: trust_types::Symbol::intern("rank"),
        location: native_trust_ir_test_span(30),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }];
    let bundle = trust_mir_extract::function_to_verifier_api_bundle_with_crate_name(
        &function,
        &compiler_contracts,
        &vcs,
        "sealed_dyn_probe",
    );
    let expected_function = trust_verifier_api::FunctionContext {
        crate_name: "sealed_dyn_probe".to_string(),
        path: function.def_path.clone(),
    };
    let expected_execution_context =
        trust_router::VerifierExecutionContext::new("impl-method-fresh-rekey-test").snapshot();
    let snapshot = exact_fresh_vc_rekey_snapshot_with_expected_function(
        &function,
        &compiler_contracts,
        &bundle,
        &vcs,
        &expected_function,
        expected_execution_context.clone(),
    );
    assert!(snapshot.complete, "exact impl-method crate identity must retain fresh re-keying");

    let mut wrong_subject = bundle.clone();
    let trust_verifier_api::BundleSubject::Function { crate_name, .. } = &mut wrong_subject.subject
    else {
        panic!("function bundle subject")
    };
    *crate_name = "attacker".to_string();
    assert!(
        !exact_fresh_vc_rekey_snapshot_with_expected_function(
            &function,
            &compiler_contracts,
            &wrong_subject,
            &vcs,
            &expected_function,
            expected_execution_context.clone(),
        )
        .complete,
        "subject crate mutation must invalidate exact fresh re-keying"
    );

    let mut wrong_context = bundle.clone();
    let vc_obligation = wrong_context
        .obligations
        .iter_mut()
        .find(|obligation| {
            matches!(
                exactly_one_obligation_context(obligation).map(|context| context.origin),
                Some(trust_verifier_api::ObligationOrigin::VerificationCondition { .. })
            )
        })
        .expect("generated VC obligation");
    mutate_test_obligation_context(vc_obligation, |context| {
        context.function.as_mut().expect("function context").crate_name = "attacker".to_string();
    });
    assert!(
        !exact_fresh_vc_rekey_snapshot_with_expected_function(
            &function,
            &compiler_contracts,
            &wrong_context,
            &vcs,
            &expected_function,
            expected_execution_context.clone(),
        )
        .complete,
        "obligation-context crate mutation must invalidate exact fresh re-keying"
    );

    let mut jointly_mutated = bundle.clone();
    let trust_verifier_api::BundleSubject::Function { crate_name, .. } =
        &mut jointly_mutated.subject
    else {
        panic!("function bundle subject")
    };
    *crate_name = "attacker".to_string();
    for obligation in &mut jointly_mutated.obligations {
        if exactly_one_obligation_context(obligation).is_some() {
            mutate_test_obligation_context(obligation, |context| {
                context.function.as_mut().expect("function context").crate_name =
                    "attacker".to_string();
            });
        }
    }
    assert!(
        !exact_fresh_vc_rekey_snapshot_with_expected_function(
            &function,
            &compiler_contracts,
            &jointly_mutated,
            &vcs,
            &expected_function,
            expected_execution_context,
        )
        .complete,
        "joint subject/context mutation must not redefine compiler-owned crate identity"
    );
}

#[test]
fn fresh_vc_rekey_seals_temporal_engine_hardened_and_unsupported_metadata_families() {
    let (temporal_function, temporal_vcs, temporal_bundle) = single_fresh_vc_binding_fixture(
        VcKind::Temporal { property: "AG ready".to_string(), machine: None },
        Formula::Bool(true),
        30,
    );
    let temporal = exact_fresh_test_obligation(&temporal_function, &temporal_vcs, &temporal_bundle);
    assert_fresh_metadata_key_is_sealed(
        &temporal_function,
        &temporal_vcs,
        temporal,
        trust_types::TY_TEMPORAL_MODEL_METADATA_KEY,
    );
    let mut temporal_error_alternative = temporal.clone();
    temporal_error_alternative.metadata.push(trust_verifier_api::MetadataEntry {
        key: format!("{}.serialize_error", trust_types::TY_TEMPORAL_MODEL_METADATA_KEY),
        value: "forged serialization failure".to_string(),
    });
    assert_eq!(
        exact_fresh_vc_index_for_obligation_without_multiplicity(
            &temporal_function,
            &temporal_error_alternative,
            &temporal_vcs,
        ),
        None,
        "a serialized temporal model cannot acquire the mutually exclusive error carrier"
    );

    let (engine_function, engine_vcs, engine_bundle) = fresh_nonlegacy_vc_binding_fixture();
    let engine = exact_fresh_test_obligation(&engine_function, &engine_vcs, &engine_bundle);
    assert_fresh_metadata_key_is_sealed(
        &engine_function,
        &engine_vcs,
        engine,
        TRUST_VC_ENGINE_TRUST_VC_FORMULA_SCHEMA_METADATA_KEY,
    );

    let (deductive_function, deductive_vcs, deductive_bundle) = single_fresh_vc_binding_fixture(
        VcKind::Postcondition,
        Formula::Ge(
            Box::new(Formula::Var("result".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        33,
    );
    let deductive =
        exact_fresh_test_obligation(&deductive_function, &deductive_vcs, &deductive_bundle);
    for key in [
        TRUST_VC_ENGINE_TRUST_MC_FORMULA_SCHEMA_METADATA_KEY,
        TRUST_VC_ENGINE_TRUST_WP_FORMULA_SCHEMA_METADATA_KEY,
    ] {
        assert_fresh_metadata_key_is_sealed(&deductive_function, &deductive_vcs, deductive, key);
    }

    let (hardened_function, hardened_vcs, hardened_bundle) = single_fresh_vc_binding_fixture(
        VcKind::UnsafeOperation { desc: "privileged instruction".to_string() },
        Formula::Bool(true),
        31,
    );
    let hardened = exact_fresh_test_obligation(&hardened_function, &hardened_vcs, &hardened_bundle);
    for key in [
        TRUST_VC_HARDENED_CATEGORY_METADATA_KEY,
        TRUST_VC_HARDENED_FAMILY_METADATA_KEY,
        TRUST_VC_HARDENED_CALLEE_METADATA_KEY,
        TRUST_VC_HARDENED_DETAIL_METADATA_KEY,
    ] {
        assert_fresh_metadata_key_is_sealed(&hardened_function, &hardened_vcs, hardened, key);
    }

    // The legacy functional-correctness encoding has a hardened category and
    // family but no concrete boundary callee/detail. Absence is semantic too:
    // a returned row may not inject those optional routing companions.
    let (category_only_function, category_only_vcs, category_only_bundle) =
        single_fresh_vc_binding_fixture(
            VcKind::FunctionalCorrectness {
                property: "hardened::process_semantics".to_string(),
                context: "category-only hardening fixture".to_string(),
            },
            Formula::Bool(true),
            34,
        );
    let category_only = exact_fresh_test_obligation(
        &category_only_function,
        &category_only_vcs,
        &category_only_bundle,
    );
    for key in [TRUST_VC_HARDENED_CATEGORY_METADATA_KEY, TRUST_VC_HARDENED_FAMILY_METADATA_KEY] {
        assert_fresh_metadata_key_is_sealed(
            &category_only_function,
            &category_only_vcs,
            category_only,
            key,
        );
    }
    for key in [TRUST_VC_HARDENED_CALLEE_METADATA_KEY, TRUST_VC_HARDENED_DETAIL_METADATA_KEY] {
        assert!(category_only.metadata.iter().all(|entry| entry.key != key));
        let mut injected = category_only.clone();
        injected.metadata.push(trust_verifier_api::MetadataEntry {
            key: key.to_string(),
            value: "forged optional hardened companion".to_string(),
        });
        assert_eq!(
            exact_fresh_vc_index_for_obligation_without_multiplicity(
                &category_only_function,
                &injected,
                &category_only_vcs,
            ),
            None,
            "injecting absent hardened companion `{key}` must fail closed",
        );
    }

    let (unsupported_function, unsupported_vcs, unsupported_bundle) =
        single_fresh_vc_binding_fixture(VcKind::UseAfterFree, Formula::Bool(true), 32);
    let unsupported =
        exact_fresh_test_obligation(&unsupported_function, &unsupported_vcs, &unsupported_bundle);
    assert_fresh_metadata_key_is_sealed(
        &unsupported_function,
        &unsupported_vcs,
        unsupported,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY,
    );
    for key in [
        TRUST_VC_CONDITION_ORIGIN_METADATA_KEY,
        TRUST_VC_PROOF_OBLIGATION_METADATA_KEY,
        TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
    ] {
        let mut forged_supported = unsupported.clone();
        forged_supported.metadata.push(trust_verifier_api::MetadataEntry {
            key: key.to_string(),
            value: "forged supported proof-unit companion".to_string(),
        });
        assert_eq!(
            exact_fresh_vc_index_for_obligation_without_multiplicity(
                &unsupported_function,
                &forged_supported,
                &unsupported_vcs,
            ),
            None,
            "unsupported TrustVC proof units cannot acquire `{key}`"
        );
    }
}

#[test]
fn fresh_vc_rekey_invalidates_legacy_compatible_proofs_and_retains_missing_vcs() {
    let (function, compiler_contracts, vcs) = native_trust_ir_compiler_function();
    let fresh_vcs = vec![vcs[0].clone()];
    let (bundle, _) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &fresh_vcs);
    let obligation = exact_fresh_test_obligation(&function, &fresh_vcs, &bundle);
    assert_eq!(
        legacy_vc_from_api_obligation(&function, obligation).formula,
        fresh_vcs[0].formula,
        "fixture must exercise the legacy-compatible bypass, not Bool(false) fallback"
    );
    let expected_context =
        trust_router::VerifierExecutionContext::new("fresh-vc-strict-proof-test").snapshot();
    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &fresh_vcs,
        expected_context.clone(),
    );
    assert!(snapshot.complete, "compiler-built inventory must snapshot exactly");
    let run = fresh_test_run_with_one_strict_proof(
        &bundle,
        &obligation.obligation_id,
        expected_context.clone(),
    );
    let (mapped, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function, &bundle, &run, &fresh_vcs, &snapshot,
    );
    assert!(
        mapped.iter().any(|(vc, result)| {
            vc.location == fresh_vcs[0].location
                && matches!(result, VerificationResult::Proved { .. })
        }),
        "untampered strict evidence must prove the exact fresh row"
    );
    assert!(bindings.iter().any(Option::is_some));

    // The public request is unchanged and still carries a valid strict proof,
    // but a compiler transform after dispatch must not replace the private VC
    // at the snapshotted index. Without an exact fresh-carrier seal this would
    // re-key the proof above onto the new `true` violation formula.
    let mut changed_fresh_vcs = fresh_vcs.clone();
    changed_fresh_vcs[0].formula = Formula::Bool(true);
    assert!(
        !exact_fresh_vc_rekey_run_is_complete(&bundle, &run, &changed_fresh_vcs, &snapshot,),
        "post-dispatch compiler VC mutation must invalidate the frozen carrier",
    );
    let (changed_mapped, changed_bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &run,
        &changed_fresh_vcs,
        &snapshot,
    );
    assert!(
        changed_mapped
            .iter()
            .all(|(_, result)| { matches!(result, VerificationResult::Unknown { .. }) })
    );
    assert!(changed_mapped.iter().any(|(vc, result)| {
        vc.formula == Formula::Bool(true)
            && matches!(result, VerificationResult::Unknown { solver, .. }
                if solver.as_str() == "trust-fresh-vc-rekey-integrity")
    }));
    assert!(changed_bindings.iter().all(Option::is_none));

    let assert_invalid = |tampered_bundle: &trust_verifier_api::TrustContractBundle,
                          tampered_run: &trust_verifier_api::VerificationRunResult,
                          label: &str| {
        let (mapped, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
            &function,
            tampered_bundle,
            tampered_run,
            &fresh_vcs,
            &snapshot,
        );
        let public_rows = tampered_bundle
            .obligations
            .iter()
            .filter(|obligation| !obligation.is_default_admission())
            .count();
        assert!(
            mapped.len() >= public_rows + snapshot.expected_vc_count + 1,
            "{label}: public/native-only rows, compiler VCs, and integrity sentinel must all remain accountable"
        );
        assert!(
            mapped.iter().all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
                && mapped.iter().any(|(vc, _)| {
                    vc.location == fresh_vcs[0].location && vc.formula == fresh_vcs[0].formula
                }),
            "{label}: no native Proved result may survive a rejected snapshot"
        );
        assert!(
            mapped.iter().any(|(vc, result)| {
                matches!(
                    (&vc.kind, &vc.formula, result),
                    (
                        VcKind::UnsupportedMir { kind, .. },
                        Formula::Bool(true),
                        VerificationResult::Unknown { .. }
                    ) if kind == "fresh-vc-rekey-integrity"
                )
            }),
            "{label}: an unpromotable integrity row must remain visible"
        );
        assert!(bindings.iter().all(Option::is_none), "{label}: bridge authority must be absent");
    };

    // Every compiler-dispatched execution-context field is part of the exact
    // re-key capability. Rebuild each result so the public envelope remains
    // fully self-consistent; only equality with the private dispatch snapshot
    // should make these otherwise-valid replay attempts fail closed.
    let rebuild_with_context = |context| {
        trust_verifier_api::VerificationRunResult::from_evidence(
            context,
            &bundle,
            run.engine.clone(),
            &run.requested_obligations,
            run.evidence.clone(),
        )
    };
    let mut replay_context = expected_context.clone();
    replay_context.run_id.push_str("-replayed");
    let replayed_run = rebuild_with_context(replay_context);
    assert!(replayed_run.validate_derived_state().is_ok());
    assert_invalid(&bundle, &replayed_run, "joint run-id/context replay");

    let mut invocation_context = expected_context.clone();
    invocation_context.invocation = trust_verifier_api::VerifierInvocation::DscanPreflight;
    let invocation_run = rebuild_with_context(invocation_context);
    assert!(invocation_run.validate_derived_state().is_ok());
    assert_invalid(&bundle, &invocation_run, "invocation-lane replay");

    let mut limits_context = expected_context.clone();
    limits_context.limits.wall_time_ms = Some(1);
    let limits_run = rebuild_with_context(limits_context);
    assert!(limits_run.validate_derived_state().is_ok());
    assert_invalid(&bundle, &limits_run, "resource-limit replay");

    let mut cancellation_context = expected_context.clone();
    cancellation_context.cancellation = trust_verifier_api::CancellationSnapshot {
        requested: true,
        reason: Some(trust_verifier_api::CancellationReason::UserRequested),
    };
    let cancellation_run = rebuild_with_context(cancellation_context);
    assert!(cancellation_run.validate_derived_state().is_ok());
    assert_invalid(&bundle, &cancellation_run, "cancellation-state replay");

    let mut metadata_context = expected_context.clone();
    metadata_context.metadata.push(trust_verifier_api::MetadataEntry {
        key: "trust.test.replayed_execution_context".to_string(),
        value: "mutated".to_string(),
    });
    let metadata_run = rebuild_with_context(metadata_context);
    assert!(metadata_run.validate_derived_state().is_ok());
    assert_invalid(&bundle, &metadata_run, "execution-metadata replay");

    let mut injected_bundle_metadata = bundle.clone();
    injected_bundle_metadata.metadata.push(trust_verifier_api::MetadataEntry {
        key: trust_verifier_api::SUMMARY_FACT_METADATA_KEY.to_string(),
        value: serde_json::to_string(&fresh_rekey_tampered_summary_fact())
            .expect("summary fact JSON"),
    });
    assert_invalid(&injected_bundle_metadata, &run, "bundle proof-input injection");
    let (mut promoted_after_integrity_failure, failed_bindings) =
        full_verification_legacy_results_bound_with_fresh_vcs(
            &function,
            &injected_bundle_metadata,
            &run,
            &fresh_vcs,
            &snapshot,
        );
    promote_structurally_dead_unreachable(&mut promoted_after_integrity_failure, None);
    promote_kernel_certifiable(&mut promoted_after_integrity_failure, None);
    let sentinel_index = promoted_after_integrity_failure
        .iter()
        .position(|(vc, _)| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "fresh-vc-rekey-integrity"
            )
        })
        .expect("integrity sentinel after promotion passes");
    assert!(matches!(
        promoted_after_integrity_failure[sentinel_index].1,
        VerificationResult::Unknown { .. }
    ));
    let no_kernel_evidence = vec![None; promoted_after_integrity_failure.len()];
    let authorities = build_result_proof_authorities(
        &promoted_after_integrity_failure,
        &failed_bindings,
        Some(&run),
        &no_kernel_evidence,
    );
    assert!(authorities.iter().all(Option::is_none));

    let referenced_contract_id = obligation.contract_id.as_deref().expect("synthetic contract");
    let mut repointed_contract = bundle.clone();
    let contract = repointed_contract
        .contracts
        .iter_mut()
        .find(|contract| contract.contract_id == referenced_contract_id)
        .expect("referenced synthetic contract");
    contract.predicate = trust_verifier_api::ContractPredicate::Unsupported {
        reason: "forged easier post-snapshot claim".to_string(),
    };
    assert_invalid(&repointed_contract, &run, "referenced contract mutation");

    let mut tampered_requested = run.clone();
    tampered_requested
        .requested_obligations
        .iter_mut()
        .find(|requested| requested.obligation_id == obligation.obligation_id)
        .expect("requested fresh row")
        .description
        .push_str("-tampered");
    assert_invalid(&bundle, &tampered_requested, "returned request mutation");

    let mut missing_requested = run.clone();
    missing_requested
        .requested_obligations
        .retain(|requested| requested.obligation_id != obligation.obligation_id);
    assert_invalid(&bundle, &missing_requested, "returned request removal");

    let mut duplicate_requested = run.clone();
    duplicate_requested.requested_obligations.push(obligation.clone());
    assert_invalid(&bundle, &duplicate_requested, "returned request duplication");

    // A verifier can construct a perfectly self-consistent public envelope
    // containing an extra obligation and matching Unsupported evidence. That
    // row was never dispatched by the compiler, so derived-state consistency
    // alone must not let the response retain any fresh-context authority.
    let mut foreign_obligation = obligation.clone();
    foreign_obligation.obligation_id = "foreign-post-dispatch-obligation".to_string();
    foreign_obligation.description = "invented after compiler dispatch".to_string();
    let mut foreign_evidence = unsupported_evidence_for(&foreign_obligation);
    foreign_evidence.engine = run.engine.clone();
    let mut foreign_requested = run.requested_obligations.clone();
    foreign_requested.push(foreign_obligation.clone());
    let mut foreign_evidence_rows = run.evidence.clone();
    foreign_evidence_rows.push(foreign_evidence);
    let foreign_run = trust_verifier_api::VerificationRunResult::from_evidence(
        run.context.clone(),
        &bundle,
        run.engine.clone(),
        &foreign_requested,
        foreign_evidence_rows,
    );
    assert!(
        foreign_run.validate_derived_state().is_ok(),
        "fixture must isolate exact dispatch-envelope closure from public derived-state checks"
    );
    assert_invalid(&bundle, &foreign_run, "returned foreign obligation injection");

    // Mutating the current bundle and returning a response that exactly agrees
    // with that mutation is still post-snapshot drift. Bind the check to the
    // compiler-dispatched inventory, not merely to bundle/run agreement at use.
    let mut foreign_bundle = bundle.clone();
    foreign_bundle.obligations.push(foreign_obligation);
    let foreign_bundle_evidence = foreign_bundle
        .obligations
        .iter()
        .map(|row| {
            if row.obligation_id == obligation.obligation_id {
                run.evidence
                    .iter()
                    .find(|evidence| evidence.obligation_id == obligation.obligation_id)
                    .expect("original strict proof")
                    .clone()
            } else {
                let mut evidence = unsupported_evidence_for(row);
                evidence.engine = run.engine.clone();
                evidence
            }
        })
        .collect::<Vec<_>>();
    let foreign_bundle_run = trust_verifier_api::VerificationRunResult::from_evidence(
        run.context.clone(),
        &foreign_bundle,
        run.engine.clone(),
        &foreign_bundle.obligations,
        foreign_bundle_evidence,
    );
    assert!(foreign_bundle_run.validate_derived_state().is_ok());
    assert_invalid(
        &foreign_bundle,
        &foreign_bundle_run,
        "post-snapshot bundle and response injection",
    );

    let mut changed_requested_id = run.clone();
    changed_requested_id
        .requested_obligations
        .iter_mut()
        .find(|requested| requested.obligation_id == obligation.obligation_id)
        .expect("requested fresh row")
        .obligation_id
        .push_str("-tampered");
    assert_invalid(&bundle, &changed_requested_id, "returned request ID mutation");

    let mut changed_run_bundle_id = run.clone();
    changed_run_bundle_id.bundle_id.push_str("-replayed");
    assert_invalid(&bundle, &changed_run_bundle_id, "returned bundle ID replay");

    let mut changed_run_subject = run.clone();
    changed_run_subject.subject = trust_verifier_api::BundleSubject::Artifact {
        name: "replayed-subject".to_string(),
        kind: "test".to_string(),
    };
    assert_invalid(&bundle, &changed_run_subject, "returned subject replay");

    let mut stale_run_summary = run.clone();
    stale_run_summary.summary.unknown = stale_run_summary.summary.unknown.saturating_add(1);
    assert_invalid(&bundle, &stale_run_summary, "stale returned derived state");

    let mut missing_bundle = bundle.clone();
    missing_bundle.obligations.retain(|row| row.obligation_id != obligation.obligation_id);
    let missing_snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &missing_bundle,
        &fresh_vcs,
        expected_context.clone(),
    );
    assert!(!missing_snapshot.complete, "missing compiler row must make snapshot incomplete");
    let (missing_mapped, missing_bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &missing_bundle,
        &run,
        &fresh_vcs,
        &missing_snapshot,
    );
    assert!(missing_mapped.iter().any(|(vc, result)| {
        vc.location == fresh_vcs[0].location
            && vc.formula == fresh_vcs[0].formula
            && matches!(result, VerificationResult::Unknown { .. })
    }));
    assert!(
        missing_mapped
            .iter()
            .all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
    );
    assert!(missing_bindings.iter().all(Option::is_none));

    let mut malformed_bundle = bundle.clone();
    let malformed = malformed_bundle
        .obligations
        .iter_mut()
        .find(|row| row.obligation_id == obligation.obligation_id)
        .expect("fresh row");
    mutate_test_obligation_context(malformed, |context| {
        context.producer = trust_verifier_api::ObligationProducer::VcGenerator;
    });
    let malformed_snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &malformed_bundle,
        &fresh_vcs,
        expected_context,
    );
    assert!(!malformed_snapshot.complete, "malformed fresh origin must fail the snapshot");
    let (malformed_mapped, malformed_bindings) =
        full_verification_legacy_results_bound_with_fresh_vcs(
            &function,
            &malformed_bundle,
            &run,
            &fresh_vcs,
            &malformed_snapshot,
        );
    assert!(malformed_mapped.iter().any(|(vc, result)| {
        vc.location == fresh_vcs[0].location
            && vc.formula == fresh_vcs[0].formula
            && matches!(result, VerificationResult::Unknown { .. })
    }));
    assert!(
        malformed_mapped
            .iter()
            .all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
    );
    assert!(malformed_bindings.iter().all(Option::is_none));
}

#[test]
fn fresh_vc_snapshot_preserves_exact_definition_entry_assumption_exclusion() {
    let (function, compiler_contracts) = requires_marker_function();
    let vcs = trust_vcgen::generate_vcs(&function);
    assert_eq!(vcs.len(), 1, "fixture must contain one regenerated requires row");
    assert!(matches!(
        (&vcs[0].kind, &vcs[0].formula),
        (VcKind::Precondition { callee }, Formula::Bool(false)) if callee == &function.name
    ));
    let (bundle, _, definition_entry_markers) =
        build_full_verification_input_for_tests_with_definition_entry_markers(
            &function,
            &compiler_contracts,
            &vcs,
        );
    let dispatched = full_verification_dispatched_obligations(&bundle, &definition_entry_markers);
    assert!(
        dispatched.iter().all(|obligation| !is_definition_site_requires_marker(obligation)),
        "the definition-entry assumption must not be a proof request"
    );
    assert!(
        dispatched.iter().all(trust_verifier_api::TrustObligation::is_default_admission),
        "only the synthetic native-bundle admission may remain in this fixture"
    );
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        panic!("function bundle subject")
    };
    let expected_function =
        trust_verifier_api::FunctionContext { crate_name: crate_name.clone(), path: path.clone() };
    let authority = CompilerFunctionAuthority::compatibility_for_test(expected_function);
    let expected_execution_context =
        trust_router::VerifierExecutionContext::new("requires-exclusion-snapshot-test").snapshot();
    let snapshot = exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
        &function,
        &compiler_contracts,
        &bundle,
        &dispatched,
        &vcs,
        definition_entry_markers,
        &authority,
        expected_execution_context.clone(),
    );
    assert!(snapshot.complete);
    assert_eq!(snapshot.expected_vc_count, 0);
    assert!(snapshot.eligible_vc_indices.is_empty());
    assert_eq!(snapshot.catalog_obligations, bundle.obligations);
    assert_eq!(snapshot.dispatched_obligations, dispatched);
    assert!(bundle.metadata.iter().any(|entry| {
        entry.key == "trust.contract.definition_site_preconditions_excluded" && entry.value == "1"
    }));

    let engine = trust_verifier_api::EngineManifest::new(
        "trust-full-verifier",
        trust_verifier_api::API_VERSION,
        trust_verifier_api::EngineKind::Composite,
    );
    let run = trust_verifier_api::VerificationRunResult::from_evidence(
        expected_execution_context,
        &bundle,
        engine,
        &dispatched,
        Vec::new(),
    );
    assert!(exact_fresh_vc_rekey_run_is_complete(&bundle, &run, &vcs, &snapshot));
    let (mapped, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function, &bundle, &run, &vcs, &snapshot,
    );
    assert!(mapped.iter().any(|(_, result)| is_entry_assumption_discharge(result)));
    assert!(bindings.iter().any(Option::is_some));
    assert!(!mapped.iter().any(|(_, result)| {
        matches!(result, VerificationResult::Unknown { solver, .. }
            if solver.as_str() == "trust-fresh-vc-rekey-integrity")
    }));

    let unexpectedly_reintroduced = trust_mir_extract::function_to_verifier_api_bundle(
        &function,
        &compiler_contracts,
        &[vcs[0].clone(), vcs[0].clone()],
    );
    let zero_eligible_snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &unexpectedly_reintroduced,
        &vcs,
        run.context.clone(),
    );
    assert!(
        !zero_eligible_snapshot.complete,
        "a nominally excluded row that unexpectedly reappears must violate the zero-row bijection"
    );
}

#[test]
fn definition_entry_marker_seal_rejects_mutation_forgery_and_duplicates() {
    let (function, compiler_contracts) = requires_marker_function();
    let (bundle, _, definition_entry_markers) =
        build_full_verification_input_for_tests_with_definition_entry_markers(
            &function,
            &compiler_contracts,
            &[],
        );
    let marker_index = bundle
        .obligations
        .iter()
        .position(is_definition_site_requires_marker)
        .expect("definition-entry marker");
    let marker = bundle.obligations[marker_index].clone();
    assert!(definition_entry_markers.matches(marker_index, &bundle, &marker));
    assert!(
        !full_verification_dispatched_obligations(&bundle, &definition_entry_markers)
            .iter()
            .any(|obligation| obligation.obligation_id == marker.obligation_id)
    );

    let assert_rejected = |name: &str, mutated: trust_verifier_api::TrustContractBundle| {
        assert!(
            !definition_entry_markers.matches(
                marker_index,
                &mutated,
                &mutated.obligations[marker_index],
            ),
            "mutation `{name}` must revoke the frozen marker",
        );
        assert!(
            full_verification_dispatched_obligations(&mutated, &definition_entry_markers)
                .iter()
                .any(|obligation| {
                    obligation.obligation_id == mutated.obligations[marker_index].obligation_id
                }),
            "mutation `{name}` must remain a proof request",
        );
    };

    let mut source_mutation = bundle.clone();
    source_mutation.obligations[marker_index].source.line = Some(usize::MAX as u32);
    assert_rejected("source", source_mutation);

    let mut digest_mutation = bundle.clone();
    digest_mutation.obligations[marker_index]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY)
        .expect("source digest")
        .value = "f".repeat(64);
    assert_rejected("source digest", digest_mutation);

    let mut context_index_mutation = bundle.clone();
    mutate_test_obligation_context(
        &mut context_index_mutation.obligations[marker_index],
        |context| {
            let trust_verifier_api::ObligationOrigin::Contract { contract_index, .. } =
                &mut context.origin
            else {
                panic!("definition-entry origin")
            };
            *contract_index += 1;
        },
    );
    assert!(is_definition_site_requires_marker(&context_index_mutation.obligations[marker_index]));
    assert_rejected("contract index", context_index_mutation);

    let mut context_function_mutation = bundle.clone();
    mutate_test_obligation_context(
        &mut context_function_mutation.obligations[marker_index],
        |context| {
            context.function.as_mut().expect("function context").path.push_str("::forged");
        },
    );
    assert!(is_definition_site_requires_marker(
        &context_function_mutation.obligations[marker_index]
    ));
    assert_rejected("context function", context_function_mutation);

    let mut context_producer_mutation = bundle.clone();
    mutate_test_obligation_context(
        &mut context_producer_mutation.obligations[marker_index],
        |context| context.producer = trust_verifier_api::ObligationProducer::Compatibility,
    );
    assert_rejected("context producer", context_producer_mutation);

    let mut context_schema_mutation = bundle.clone();
    mutate_test_obligation_context(
        &mut context_schema_mutation.obligations[marker_index],
        |context| context.schema_version.push_str("-forged"),
    );
    assert_rejected("context schema", context_schema_mutation);

    let marker_contract_id = marker.contract_id.as_deref().expect("marker contract");
    let mut predicate_mutation = bundle.clone();
    predicate_mutation
        .contracts
        .iter_mut()
        .find(|contract| contract.contract_id == marker_contract_id)
        .expect("marker contract")
        .predicate = trust_verifier_api::ContractPredicate::TrustExpr { text: "true".to_string() };
    assert_rejected("contract predicate", predicate_mutation);

    let mut forged_bundle = bundle.clone();
    let mut forged_contract = forged_bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == marker_contract_id)
        .expect("marker contract")
        .clone();
    forged_contract.contract_id.push_str(":forged");
    let mut forged = marker.clone();
    forged.obligation_id.push_str(":forged");
    forged.contract_id = Some(forged_contract.contract_id.clone());
    mutate_test_obligation_context(&mut forged, |context| {
        let trust_verifier_api::ObligationOrigin::Contract { contract_id, .. } =
            &mut context.origin
        else {
            panic!("definition-entry origin")
        };
        *contract_id = forged_contract.contract_id.clone();
    });
    assert!(
        is_definition_site_requires_marker(&forged),
        "the attack must be a self-consistent public Contract{{Requires}} carrier",
    );
    forged_bundle.contracts.push(forged_contract);
    forged_bundle.obligations.push(forged.clone());
    let forged_index = forged_bundle.obligations.len() - 1;
    assert!(!definition_entry_markers.matches(forged_index, &forged_bundle, &forged));
    let forged_vc = legacy_vc_from_api_obligation(&function, &forged);
    assert!(
        result_obligation_binding(forged_index, &forged_vc, &forged)
            .is_some_and(|binding| !binding.definition_entry_assumption),
        "public same-shape drift cannot flip the compiler-private frozen bit",
    );
    let forged_dispatch =
        full_verification_dispatched_obligations(&forged_bundle, &definition_entry_markers);
    assert!(forged_dispatch.iter().any(|obligation| obligation == &forged));
    assert!(
        forged_dispatch.iter().all(|obligation| obligation.obligation_id != marker.obligation_id),
        "a forged extra row cannot revoke the authentic row's exact frozen classification",
    );

    let mut duplicated = bundle.clone();
    duplicated.obligations.push(marker.clone());
    assert!(
        !definition_entry_markers.matches(
            marker_index,
            &duplicated,
            &duplicated.obligations[marker_index],
        ),
        "duplicate exact IDs must revoke even the original positional marker",
    );
    assert_eq!(
        full_verification_dispatched_obligations(&duplicated, &definition_entry_markers)
            .iter()
            .filter(|obligation| obligation.obligation_id == marker.obligation_id)
            .count(),
        2,
        "both ambiguous rows must remain proof requests",
    );

    let mut reordered = bundle.clone();
    let other_index = reordered
        .obligations
        .iter()
        .position(|obligation| obligation.obligation_id != marker.obligation_id)
        .expect("native admission row");
    reordered.obligations.swap(marker_index, other_index);
    assert!(
        full_verification_dispatched_obligations(&reordered, &definition_entry_markers)
            .iter()
            .any(|obligation| obligation.obligation_id == marker.obligation_id),
        "a reordered public marker cannot carry positional skip authority",
    );
}

#[test]
fn fresh_catalog_dispatch_keeps_recursive_self_precondition_as_a_proof_request() {
    let (function, compiler_contracts) = requires_marker_function();
    let definition_row = trust_vcgen::generate_vcs(&function)
        .into_iter()
        .next()
        .expect("definition-entry requires row");
    // Adversarial recursive-call shape: same function/callee/location and the
    // same constant-false compatibility formula. Only the compiler-owned dense
    // source-clause provenance distinguishes the definition marker.
    let mut recursive_call = definition_row.clone();
    recursive_call.contract_metadata = None;
    let all_vcs = vec![definition_row, recursive_call.clone()];

    let (bundle, _, definition_entry_markers) =
        build_full_verification_input_for_tests_with_definition_entry_markers(
            &function,
            &compiler_contracts,
            &all_vcs,
        );
    let marker = bundle
        .obligations
        .iter()
        .find(|obligation| is_definition_site_requires_marker(obligation))
        .expect("definition-entry catalog marker");
    let recursive_public = bundle
        .obligations
        .iter()
        .find(|obligation| {
            exactly_one_obligation_context(obligation).is_some_and(|context| {
                matches!(
                    context.origin,
                    trust_verifier_api::ObligationOrigin::VerificationCondition { vc_index: 1, .. }
                )
            })
        })
        .expect("recursive call-site public VC");
    let dispatched = full_verification_dispatched_obligations(&bundle, &definition_entry_markers);
    assert!(dispatched.iter().all(|obligation| obligation.obligation_id != marker.obligation_id));
    assert!(
        dispatched
            .iter()
            .any(|obligation| { obligation.obligation_id == recursive_public.obligation_id })
    );

    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        panic!("function bundle subject")
    };
    let expected_function =
        trust_verifier_api::FunctionContext { crate_name: crate_name.clone(), path: path.clone() };
    let authority = CompilerFunctionAuthority::compatibility_for_test(expected_function);
    let expected_execution_context =
        trust_router::VerifierExecutionContext::new("recursive-requires-dispatch-test").snapshot();
    let snapshot = exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
        &function,
        &compiler_contracts,
        &bundle,
        &dispatched,
        &all_vcs,
        definition_entry_markers,
        &authority,
        expected_execution_context.clone(),
    );
    assert!(snapshot.complete);
    assert_eq!(snapshot.expected_vc_count, 1);
    assert_eq!(snapshot.eligible_vc_indices, vec![1]);

    let evidence = dispatched.iter().map(unsupported_evidence_for).collect::<Vec<_>>();
    let run = trust_verifier_api::VerificationRunResult::from_evidence(
        expected_execution_context,
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &dispatched,
        evidence,
    );
    assert!(exact_fresh_vc_rekey_run_is_complete(&bundle, &run, &all_vcs, &snapshot));
    let (results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function, &bundle, &run, &all_vcs, &snapshot,
    );
    let authorities =
        build_result_proof_authorities(&results, &bindings, Some(&run), &vec![None; results.len()]);
    let proof_results = build_proof_results_with_runtime_checks(
        false,
        &results,
        &[],
        &bindings,
        &authorities,
        Some(&function),
    );
    let marker_index = bindings
        .iter()
        .position(|binding| {
            binding
                .as_ref()
                .is_some_and(|binding| binding.public_obligation_id == marker.obligation_id)
        })
        .expect("marker result binding");
    let recursive_index = bindings
        .iter()
        .position(|binding| {
            binding.as_ref().is_some_and(|binding| {
                binding.public_obligation_id == recursive_public.obligation_id
            })
        })
        .expect("recursive result binding");
    assert!(matches!(
        authorities[marker_index],
        Some(ResultProofAuthority::DefinitionEntryAssumption { .. })
    ));
    assert!(authorities[recursive_index].is_none());
    assert_eq!(
        proof_results.dispositions[ObligationId::from_usize(marker_index)].status,
        TrustStatus::Trusted,
    );
    assert_eq!(
        proof_results.dispositions[ObligationId::from_usize(recursive_index)].status,
        TrustStatus::Failed,
        "an unresolved recursive self-call must not inherit the definition-entry skip",
    );
    run.validate_derived_state().expect("recursive Requires run remains canonical");
    run.try_to_manifest().expect("recursive Requires run remains manifestable");
}

#[test]
fn fresh_vc_rekey_rejects_duplicate_exact_obligations_and_maps_the_unique_row() {
    let (function, vcs, bundle) = fresh_nonlegacy_vc_binding_fixture();
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            exact_fresh_vc_index_for_obligation_without_multiplicity(&function, obligation, &vcs)
                == Some(0)
        })
        .expect("fresh VC obligation");

    let evidence = bundle.obligations.iter().map(unsupported_evidence_for).collect::<Vec<_>>();
    let run = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("fresh-vc-rekey-test").snapshot(),
        &bundle,
        evidence[0].engine.clone(),
        &bundle.obligations,
        evidence,
    );
    let compiler_contracts = trust_types::CompilerContractBundle::new(function.contracts.clone());
    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &vcs,
        run.context.clone(),
    );
    let (mapped, _) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function, &bundle, &run, &vcs, &snapshot,
    );
    let mapped_vc = mapped
        .iter()
        .map(|(vc, _)| vc)
        .find(|vc| vc.location == vcs[0].location)
        .expect("mapped fresh VC row");
    assert_eq!(
        mapped_vc.formula, vcs[0].formula,
        "the unique exact row must retain its compiler-owned formula"
    );

    let mut duplicated_bundle = bundle.clone();
    duplicated_bundle.obligations.push(obligation.clone());
    let source_digest = trust_mir_extract::verifier_source_digest(&function);
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        panic!("function bundle subject")
    };
    let expected_function =
        trust_verifier_api::FunctionContext { crate_name: crate_name.clone(), path: path.clone() };
    let authority = CompilerFunctionAuthority::compatibility_for_test(expected_function);
    let duplicated = exact_fresh_vc_match_multiplicity(
        &function,
        &duplicated_bundle,
        &vcs,
        &source_digest,
        &authority,
    );
    assert_eq!(duplicated.get(&0), Some(&2));
    assert!(
        exact_unique_fresh_vc_for_obligation(
            &function,
            obligation,
            &vcs,
            &duplicated,
            &source_digest,
        )
        .is_none(),
        "a duplicate public carrier must never select one row"
    );
    let (duplicate_mapped, _) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &duplicated_bundle,
        &run,
        &vcs,
        &snapshot,
    );
    let duplicate_rows = duplicate_mapped
        .iter()
        .filter(|(vc, _)| vc.location == vcs[0].location)
        .collect::<Vec<_>>();
    assert!(
        duplicate_rows
            .iter()
            .all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
            && duplicate_rows.iter().any(|(vc, _)| vc.formula == vcs[0].formula),
        "a duplicate public carrier must invalidate the batch without losing the compiler VC"
    );

    let encoded_summary_fact =
        serde_json::to_string(&fresh_rekey_tampered_summary_fact()).expect("summary fact JSON");
    for key in [
        trust_verifier_api::SUMMARY_FACT_METADATA_KEY,
        TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
        "trust.future.proof_input",
    ] {
        let mut injected_bundle = bundle.clone();
        injected_bundle.metadata.push(trust_verifier_api::MetadataEntry {
            key: key.to_string(),
            value: encoded_summary_fact.clone(),
        });
        let (mapped, _) = full_verification_legacy_results_bound_with_fresh_vcs(
            &function,
            &injected_bundle,
            &run,
            &vcs,
            &snapshot,
        );
        assert!(
            mapped.iter().all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
                && mapped.iter().any(|(vc, _)| {
                    vc.location == vcs[0].location && vc.formula == vcs[0].formula
                }),
            "bundle-level `{key}` proof inputs must invalidate fresh proof authority"
        );
    }
}

fn native_trust_ir_panic_function(panic_reachable: bool) -> trust_types::VerifiableFunction {
    trust_types::VerifiableFunction {
        name: "panic_branch".to_string(),
        def_path: "demo::panic_branch".to_string(),
        span: native_trust_ir_test_span(30),
        body: trust_types::VerifiableBody {
            locals: vec![trust_types::LocalDecl {
                index: 0,
                ty: trust_types::Ty::Unit,
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                trust_types::BasicBlock {
                    id: trust_types::BlockId(0),
                    stmts: Vec::new(),
                    terminator: trust_types::Terminator::SwitchInt {
                        discr: trust_types::Operand::Constant(trust_types::ConstValue::Bool(
                            panic_reachable,
                        )),
                        targets: vec![(1, trust_types::BlockId(1))],
                        otherwise: trust_types::BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: native_trust_ir_test_span(30),
                    },
                },
                trust_types::BasicBlock {
                    id: trust_types::BlockId(1),
                    stmts: Vec::new(),
                    terminator: trust_types::Terminator::Call {
                        func: "core::panicking::panic".to_string(),
                        args: Vec::new(),
                        dest: trust_types::Place::local(0),
                        target: None,
                        span: native_trust_ir_test_span(31),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                trust_types::BasicBlock {
                    id: trust_types::BlockId(2),
                    stmts: Vec::new(),
                    terminator: trust_types::Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: trust_types::Ty::Unit,
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

#[test]
fn public_native_inventory_reset_removes_all_bridge_proof_authority() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let mut module = trust_ir_bridge::lower_mir_compat_to_trust_ir(&function)
        .expect("MIR compatibility fixture should lower");
    let stale_id = module
        .proof_obligations
        .first()
        .map(|obligation| obligation.id)
        .expect("contract fixture should create a bridge-local proof obligation");

    module.proof_certificates.push(trust_ir::ProofCertificate {
        obligation: stale_id,
        prover: "stale-bridge-prover".to_string(),
        evidence: trust_ir::ProofEvidence::SmtProof(vec![1]),
    });
    module
        .obligation_diagnostics
        .push(trust_ir::ObligationDiagnostic::error(stale_id, "stale bridge diagnostic"));
    let lowered_function = module.functions.first_mut().expect("lowered function");
    lowered_function.summary = Some(trust_ir::FunctionSummary {
        requires: Vec::new(),
        ensures: Vec::new(),
        params: Vec::new(),
        proved: true,
    });
    lowered_function
        .proofs
        .extend([trust_ir::ProofAnnotation::Pure, trust_ir::ProofAnnotation::ProofRef(stale_id)]);
    let node = lowered_function
        .blocks
        .first_mut()
        .and_then(|block| block.body.first_mut())
        .expect("lowered function should contain an instruction");
    node.proofs.extend([
        trust_ir::ProofAnnotation::NoPanic,
        trust_ir::ProofAnnotation::ProofRef(stale_id),
    ]);
    node.proof_context = Some(trust_ir::proof::ProofContext {
        assumes: vec![stale_id],
        establishes: vec![stale_id],
    });

    reset_native_trust_ir_proof_inventory_to_public_bundle(&mut module);

    assert!(module.proof_obligations.is_empty());
    assert!(module.proof_certificates.is_empty());
    assert!(module.obligation_diagnostics.is_empty());
    let lowered_function = &module.functions[0];
    assert_eq!(lowered_function.summary.as_ref().map(|summary| summary.proved), Some(false));
    assert!(lowered_function.proofs.contains(&trust_ir::ProofAnnotation::Pure));
    assert!(
        lowered_function
            .proofs
            .iter()
            .all(|annotation| !matches!(annotation, trust_ir::ProofAnnotation::ProofRef(_)))
    );
    let node = &lowered_function.blocks[0].body[0];
    assert!(node.proofs.contains(&trust_ir::ProofAnnotation::NoPanic));
    assert!(
        node.proofs
            .iter()
            .all(|annotation| !matches!(annotation, trust_ir::ProofAnnotation::ProofRef(_)))
    );
    assert!(node.proof_context.is_none());
}

#[test]
fn trust_wp_trust_formula_payload_refuses_guarded_division() {
    let int_sort = trust_verifier_api::TrustSpecSort::Int;
    let numerator = trust_verifier_api::TrustSpecExpr::variable("numerator", int_sort);
    let denominator = trust_verifier_api::TrustSpecExpr::variable("denominator", int_sort);
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::And,
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Ne,
                denominator.clone(),
                trust_verifier_api::TrustSpecExpr::int_literal("0"),
            ),
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Eq,
                trust_verifier_api::TrustSpecExpr::result(int_sort),
                trust_verifier_api::TrustSpecExpr::binary(
                    trust_verifier_api::TrustSpecBinaryOp::Div,
                    numerator.clone(),
                    denominator.clone(),
                ),
            ),
        ),
        vec![
            trust_verifier_api::TrustSpecVariable {
                name: "numerator".to_string(),
                sort: int_sort,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Local { index: 0 },
            },
            trust_verifier_api::TrustSpecVariable {
                name: "denominator".to_string(),
                sort: int_sort,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Local { index: 1 },
            },
        ],
    );

    let error = trust_spec_predicate_to_trust_formula_payload(&predicate)
        .expect_err("a nonzero guard does not make unbounded-Int arithmetic machine-faithful");

    assert!(error.contains("arithmetic operator `div`"), "{error}");
    assert!(error.contains("u64::MAX"), "{error}");
    assert!(error.contains("amendment 1"), "{error}");
}

#[test]
fn trust_wp_trust_formula_payload_rejects_unguarded_division() {
    let int_sort = trust_verifier_api::TrustSpecSort::Int;
    let numerator = trust_verifier_api::TrustSpecExpr::variable("numerator", int_sort);
    let denominator = trust_verifier_api::TrustSpecExpr::variable("denominator", int_sort);
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::Eq,
            trust_verifier_api::TrustSpecExpr::result(int_sort),
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Div,
                numerator,
                denominator,
            ),
        ),
        vec![
            trust_verifier_api::TrustSpecVariable {
                name: "numerator".to_string(),
                sort: int_sort,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Local { index: 0 },
            },
            trust_verifier_api::TrustSpecVariable {
                name: "denominator".to_string(),
                sort: int_sort,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Local { index: 1 },
            },
        ],
    );

    let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
        .expect_err("unguarded division should fail closed before trust-wp native replay");

    assert!(err.contains("divisor must"), "{err}");
}

#[test]
fn trust_mc_direct_typed_chc_input_accepts_hardened_native_vc_payloads() {
    let flag = trust_verifier_api::TrustSpecExpr::variable(
        "panic_flag",
        trust_verifier_api::TrustSpecSort::Bool,
    );
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::And,
            flag.clone(),
            trust_verifier_api::TrustSpecExpr::unary(
                trust_verifier_api::TrustSpecUnaryOp::Not,
                flag,
            ),
        ),
        vec![trust_verifier_api::TrustSpecVariable {
            name: "panic_flag".to_string(),
            sort: trust_verifier_api::TrustSpecSort::Bool,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
        }],
    );
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo:panic_boundary:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.hardened".to_string(),
            name: "panic_boundary".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "panic boundary".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate)
                    .expect("TrustSpecPredicate should serialize"),
            },
        ],
    };

    let constraint = trust_mc_typed_chc_constraint_for_obligation(&obligation)
        .expect("hardened TrustSpecPredicate should lower to trust-mc typed CHC")
        .expect("hardened trust-mc obligation should emit typed CHC input");

    assert_eq!(
        constraint.vars,
        vec![serde_json::json!({
            "name": "panic_flag",
            "sort": { "kind": "bool" },
        })]
    );
    assert_eq!(constraint.constraint["kind"], "binary");
    assert_eq!(constraint.constraint["op"], "and");
    assert_eq!(constraint.constraint["rhs"]["kind"], "unary");
    assert_eq!(constraint.constraint["rhs"]["op"], "not");
}

#[test]
fn trust_mc_typed_chc_preserves_array_select_while_trust_wp_fails_closed() {
    let array_sort = trust_verifier_api::TrustSpecSort::Array {
        element: trust_verifier_api::TrustSpecScalarSort::Int,
    };
    let selected = trust_verifier_api::TrustSpecExpr::index(
        trust_verifier_api::TrustSpecExpr::variable("xs", array_sort),
        trust_verifier_api::TrustSpecExpr::int_literal("0"),
        trust_verifier_api::TrustSpecSort::Int,
    );
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::Eq,
            selected,
            trust_verifier_api::TrustSpecExpr::variable(
                "first",
                trust_verifier_api::TrustSpecSort::Int,
            ),
        ),
        vec![
            trust_verifier_api::TrustSpecVariable {
                name: "xs".to_string(),
                sort: array_sort,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
            },
            trust_verifier_api::TrustSpecVariable {
                name: "first".to_string(),
                sort: trust_verifier_api::TrustSpecSort::Int,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
            },
        ],
    );
    predicate.validate().expect("bounded public Select predicate validates");
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo:loop_invariant:array-select".to_string(),
        kind: trust_verifier_api::ObligationKind::LoopInvariant,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "array Select E4".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate).expect("predicate serializes"),
            },
        ],
    };

    let constraint = trust_mc_typed_chc_constraint_for_obligation(&obligation)
        .expect("typed array CHC lowering is well formed")
        .expect("E4 array Select remains a typed trust-mc constraint");
    assert_eq!(
        constraint.vars[0]["sort"],
        serde_json::json!({
            "kind": "array",
            "index": { "kind": "int" },
            "element": { "kind": "int" },
        })
    );
    assert_eq!(constraint.constraint["kind"], "binary");
    assert_eq!(constraint.constraint["lhs"]["kind"], "select");
    assert_eq!(constraint.constraint["lhs"]["array"]["name"], "xs");

    let wp_error = trust_spec_predicate_to_trust_formula_payload(&predicate)
        .expect_err("scalar trust-wp payload must reject public arrays");
    assert!(wp_error.contains("arrays are outside trust-wp"), "{wp_error}");

    let invalid = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::variable(
            "undeclared",
            trust_verifier_api::TrustSpecSort::Bool,
        ),
        Vec::new(),
    );
    let mut malformed_obligation = obligation;
    malformed_obligation
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
        .expect("payload metadata")
        .value = serde_json::to_string(&invalid).expect("invalid predicate serializes");
    assert!(matches!(
        trust_mc_typed_chc_lowering_for_obligation(&malformed_obligation),
        TrustMcTypedChcLowering::Unsupported(reason)
            if reason.contains("invalid TrustSpecPredicate") && reason.contains("undeclared")
    ));
}

#[test]
fn trust_mc_typed_chc_contract_binds_hardened_obligation_to_canonical_public_contract() {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();

    let original_contract_id = "contract:read_fixed_array_value:panic_boundary:source";
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-read-fixed-array-value",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    bundle.contracts.push(trust_verifier_api::TrustContract {
        contract_id: original_contract_id.to_string(),
        kind: trust_verifier_api::ContractKind::Asserts,
        predicate: trust_verifier_api::ContractPredicate::TrustExpr {
            text: "original hardened panic-boundary source context".to_string(),
        },
        source: native_trust_ir_test_source_location(17),
        metadata: Vec::new(),
    });

    let panic_flag = trust_verifier_api::TrustSpecExpr::variable(
        "panic_flag",
        trust_verifier_api::TrustSpecSort::Bool,
    );
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::And,
            panic_flag.clone(),
            trust_verifier_api::TrustSpecExpr::unary(
                trust_verifier_api::TrustSpecUnaryOp::Not,
                panic_flag,
            ),
        ),
        vec![trust_verifier_api::TrustSpecVariable {
            name: "panic_flag".to_string(),
            sort: trust_verifier_api::TrustSpecSort::Bool,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
        }],
    );
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: "vc:read_fixed_array_value:panic_boundary:1".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.hardened".to_string(),
            name: "panic_boundary".to_string(),
        },
        contract_id: Some(original_contract_id.to_string()),
        proof_item_id: None,
        source: native_trust_ir_test_source_location(17),
        description: "hardened boundary (panic_boundary): assert can panic".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_HARDENED_CATEGORY_METADATA_KEY.to_string(),
                value: "panic_boundary".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate)
                    .expect("TrustSpecPredicate should serialize"),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: "11".repeat(32),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: "22".repeat(32),
            },
        ],
    });

    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
            .expect("native TrustIr bundle should build")
            .expect("hardened panic-boundary obligation should request trust-mc");

    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == "vc:read_fixed_array_value:panic_boundary:1")
        .expect("hardened obligation should remain in public bundle");
    assert_native_proof_unit_metadata(obligation, "trust-mc");
    let synthetic_contract_id = test_obligation_metadata(
        obligation,
        super::TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY,
    );
    assert_ne!(synthetic_contract_id, original_contract_id);
    let public_contract_id = obligation
        .contract_id
        .as_deref()
        .expect("supported trust-mc lowering must link a canonical public semantic contract");
    assert!(
        public_contract_id.starts_with("contract:trust-mc-typed-chc-public:"),
        "canonical trust-mc contract ID must be derived before native identities are minted"
    );
    assert_ne!(public_contract_id, original_contract_id);
    assert_ne!(public_contract_id, synthetic_contract_id);
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_MC_TYPED_CHC_ORIGINAL_CONTRACT_METADATA_KEY,
        ),
        original_contract_id,
        "the displaced source contract must remain explicitly auditable"
    );
    assert!(
        bundle.contracts.iter().any(|contract| contract.contract_id == original_contract_id),
        "the original contract context should stay auditable in the bundle"
    );

    let public_contract =
        bundle.contracts.iter().find(|contract| contract.contract_id == public_contract_id).expect(
            "canonical trust-mc public contract should be present before transport annotation",
        );
    let trust_verifier_api::ContractPredicate::MathIr {
        schema: public_schema,
        value: public_value,
    } = &public_contract.predicate
    else {
        panic!("canonical trust-mc public contract must be typed MathIr");
    };
    assert_eq!(public_schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(public_value["obligation_id"], obligation.obligation_id);
    assert_eq!(public_value["origin"], "mir_derived");
    assert_eq!(
        public_value["function_name"], "checked_transfer",
        "public semantics must use the exact selected TrustIr function name, not the Rust def-path"
    );
    assert!(
        public_value.get("native_metadata").is_none(),
        "canonical public semantics must not depend on postbuild native transport metadata"
    );
    assert!(
        public_contract
            .metadata
            .iter()
            .all(|entry| entry.key != super::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY),
        "canonical public semantics must not carry request-derived binding metadata"
    );

    let trust_mc_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == synthetic_contract_id)
        .expect("synthetic typed trust-mc contract should be appended");
    let trust_verifier_api::ContractPredicate::MathIr { schema, value } =
        &trust_mc_contract.predicate
    else {
        panic!("typed trust-mc contract must be MathIr");
    };
    assert_eq!(schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["schema_version"], super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["origin"], "mir_derived");
    assert_eq!(
        value["vars"],
        serde_json::json!([
            { "name": "panic_flag", "sort": { "kind": "bool" } }
        ])
    );
    assert_eq!(value["rules"][0]["body"]["constraints"][0]["op"], "and");
    assert_eq!(value["native_metadata"]["producer"], "TrustIr");
    assert_eq!(value["native_metadata"]["adapter_input"], "rust-mir");
    assert_eq!(value["native_metadata"]["verification_mode"], "chc");
    let mut canonical_semantics = public_value.clone();
    canonical_semantics
        .as_object_mut()
        .expect("public typed CHC is an object")
        .remove("obligation_id");
    let mut native_semantics = value.clone();
    let native_semantics = native_semantics.as_object_mut().expect("native typed CHC is an object");
    native_semantics.remove("obligation_id");
    native_semantics.remove("native_metadata");
    assert_eq!(
        canonical_semantics,
        serde_json::Value::Object(native_semantics.clone()),
        "public and native TrustMC contracts may differ only by native identity/transport fields"
    );
    let binding_metadata = trust_mc_contract
        .metadata
        .iter()
        .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY)
        .map(|entry| entry.value.as_str())
        .expect("synthetic typed trust-mc contract should carry binding metadata");
    let binding: serde_json::Value =
        serde_json::from_str(binding_metadata).expect("binding metadata should be JSON");
    let source_digest = trust_mc_contract
        .metadata
        .iter()
        .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY)
        .map(|entry| entry.value.as_str())
        .expect("synthetic typed trust-mc contract should carry source digest");
    let synthetic_digest = trust_mc_contract
        .metadata
        .iter()
        .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY)
        .map(|entry| entry.value.as_str())
        .expect("synthetic typed trust-mc contract should carry synthetic digest");
    assert_eq!(source_digest.len(), 64);
    assert_eq!(synthetic_digest.len(), 64);
    assert_eq!(binding["schema_version"], super::TRUST_MC_TYPED_CHC_BINDING_SCHEMA);
    assert_eq!(binding["source_digest"]["value"].as_str(), Some(source_digest));
    assert_eq!(binding["synthetic_chc_digest"]["value"].as_str(), Some(synthetic_digest));
    assert_eq!(
        test_obligation_metadata(obligation, super::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY),
        binding_metadata
    );

    let trust_mc_request = native_trust_ir_bundle
        .requests
        .iter()
        .find(|request| matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustMc))
        .expect("native bundle should include a trust-mc request");
    assert_eq!(
        value["native_metadata"]["native_request_id"].as_u64(),
        Some(trust_mc_request.id().index() as u64)
    );
    assert_eq!(
        value["native_metadata"]["proof_obligation_ids"]
            .as_array()
            .and_then(|ids| ids.first())
            .and_then(|id| id.as_u64()),
        test_obligation_metadata(
            obligation,
            trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
        )
        .parse::<u64>()
        .ok()
    );
}

#[test]
fn trust_mc_default_admission_accepts_only_exact_tls_address_nodes() {
    let exact_op = trust_ir::dialect::trust_rust::thread_local_addr("test::TLS");
    let exact = trust_ir::InstrNode::new(trust_ir::Inst::DialectOp(Box::new(exact_op.clone())))
        .with_result(trust_ir::ValueId::new(0));
    assert!(
        !trust_mc_default_instruction_requires_fail_closed_admission(&exact),
        "the one-result canonical TLS-address node is the sole admitted dialect operation"
    );

    let no_result = trust_ir::InstrNode::new(trust_ir::Inst::DialectOp(Box::new(exact_op.clone())));
    assert!(trust_mc_default_instruction_requires_fail_closed_admission(&no_result));

    let two_results =
        trust_ir::InstrNode::new(trust_ir::Inst::DialectOp(Box::new(exact_op.clone())))
            .with_result(trust_ir::ValueId::new(0))
            .with_result(trust_ir::ValueId::new(1));
    assert!(trust_mc_default_instruction_requires_fail_closed_admission(&two_results));

    let mut near_miss = exact_op;
    near_miss.version = 2;
    let near_miss = trust_ir::InstrNode::new(trust_ir::Inst::DialectOp(Box::new(near_miss)))
        .with_result(trust_ir::ValueId::new(0));
    assert!(trust_mc_default_instruction_requires_fail_closed_admission(&near_miss));

    let unknown = trust_ir::InstrNode::new(trust_ir::Inst::DialectOp(Box::new(
        trust_ir::DialectInst::new("trust_rust", "unknown").with_result_ty(trust_ir::Ty::Ptr),
    )))
    .with_result(trust_ir::ValueId::new(0));
    assert!(trust_mc_default_instruction_requires_fail_closed_admission(&unknown));
}

#[test]
fn trust_mc_default_function_obligation_emits_typed_chc_request_without_contracts() {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-default-trust-mc",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );

    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
            .expect("native TrustIr bundle should build")
            .expect("default trust-mc obligation should force a native TrustIr request");

    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation
                .metadata
                .iter()
                .any(|entry| entry.key == super::TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY)
        })
        .expect("compiler should append a default trust-mc function obligation");
    assert_eq!(obligation.kind, trust_verifier_api::ObligationKind::ArithmeticSafety);
    assert_native_proof_unit_metadata(obligation, "trust-mc");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY
        ),
        "supported"
    );
    let trust_mc_contract_id = test_obligation_metadata(
        obligation,
        super::TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY,
    );
    let trust_mc_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == trust_mc_contract_id)
        .expect("default trust-mc obligation should have a synthetic typed CHC contract");
    let trust_verifier_api::ContractPredicate::MathIr { schema, value } =
        &trust_mc_contract.predicate
    else {
        panic!("default trust-mc contract must be MathIr");
    };
    assert_eq!(schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["schema_version"], super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["origin"], "mir_derived");
    assert_eq!(value["vars"], serde_json::json!([]));
    let error_rule = value["rules"]
        .as_array()
        .and_then(|rules| rules.iter().find(|rule| rule["head"]["name"] == "error"))
        .expect("default trust-mc contract should include an error rule");
    assert_eq!(error_rule["body"]["relation"]["name"], "bb0");
    assert_eq!(error_rule["body"]["constraints"][0]["kind"], "bool_const");
    assert_eq!(error_rule["body"]["constraints"][0]["value"], false);
    assert!(value.get("unsupported").is_none());
    assert!(
        native_trust_ir_bundle.requests.iter().any(|request| matches!(
            request.verifier_suite(),
            trust_ir::NativeVerifierSuite::TrustMc
        )),
        "default function obligation should create a native trust-mc request"
    );
}

#[test]
fn synthesized_panic_obligation_is_publicly_bound_and_deferred_to_typed_transport() {
    let mut module_digests = Vec::new();
    for panic_reachable in [false, true] {
        let function = native_trust_ir_panic_function(panic_reachable);
        let mut bundle = trust_verifier_api::TrustContractBundle::empty(
            format!("bundle-{}", function.name),
            trust_verifier_api::BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: function.def_path.clone(),
            },
        );

        let native_bundle =
            build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
                .expect("a synthesized panic obligation must not leave a dangling proof-item link")
                .expect("an asserted function must emit a native TrustMC request");
        native_bundle.validate().expect("synthesized panic authority must validate end to end");

        let panic_obligation = bundle
            .obligations
            .iter()
            .find(|obligation| {
                obligation_is_synthesized_whole_function_panic_freedom(
                    &function,
                    Some("demo"),
                    obligation,
                )
            })
            .unwrap_or_else(|| {
                panic!(
                    "the bridge panic site must surface as one exact counted public obligation: {:#?}",
                    bundle.obligations
                )
            });
        assert_eq!(panic_obligation.kind, trust_verifier_api::ObligationKind::Assertion);
        assert!(panic_obligation.contract_id.is_none());
        assert!(
            panic_obligation.proof_item_id.is_none(),
            "a removed bridge-local proof row must never be exposed as a public proof item"
        );
        assert_eq!(panic_obligation.source.file.as_deref(), Some("src/lib.rs"));
        assert_eq!(panic_obligation.source.line, Some(30));
        assert_eq!(
            test_obligation_metadata(
                panic_obligation,
                super::TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY,
            ),
            "unsupported",
            "no direct predicate is intentional: the adapter must defer to full-module transport"
        );

        let proof_id = test_obligation_metadata(
            panic_obligation,
            trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
        )
        .parse::<u32>()
        .map(trust_ir::ProofId::new)
        .expect("native proof ID should parse");
        let proof = native_bundle
            .module
            .proof_obligations
            .iter()
            .find(|proof| proof.id == proof_id)
            .expect("native module must contain the exact public panic proof unit");
        let source = proof.source.as_ref().expect("panic proof unit must carry typed source");
        assert_eq!(source.source_id, panic_obligation.obligation_id);
        assert_eq!(
            source.public.as_ref().map(|public| public.obligation_id.as_str()),
            Some(panic_obligation.obligation_id.as_str())
        );
        assert_eq!(
            proof.function,
            native_bundle.requests.iter().find_map(|request| {
                let trust_ir::NativeVerificationRequest::TrustMc(request) = request else {
                    return None;
                };
                request.obligations.contains(&proof_id).then_some(request.function)
            })
        );

        let lowered_function = native_bundle
            .module
            .functions
            .iter()
            .find(|lowered| lowered.name == function.name)
            .expect("selected TrustIr function should remain in the bundle");
        assert!(
            lowered_function
                .blocks
                .iter()
                .flat_map(|block| block.body.iter())
                .any(|node| matches!(node.inst, trust_ir::Inst::Assert { .. })),
            "the panic call must lower to the refutable TrustIr assertion solved by transport"
        );
        module_digests.push(native_bundle.trust_ir_module_digest);
    }
    assert_ne!(
        module_digests[0], module_digests[1],
        "unreachable and reachable panic paths must remain distinct authenticated TrustIr modules"
    );
}

#[test]
fn synthesized_panic_identity_rejects_marker_lookalikes_and_duplicates() {
    let function = native_trust_ir_panic_function(true);
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-panic-identity",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    // The empty test bundle has no crate-source metadata by default. Seed an
    // explicit, distinct bundle-level extract-time identity so this regression genuinely
    // proves that the panic aggregate cannot borrow it in place of the exact
    // function-source digest.
    let bundle_source_digest =
        trust_types::stable_sha256_hex(b"panic-identity-test-extract-source");
    bundle.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
        value: bundle_source_digest.clone(),
    });
    build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
        .expect("panic fixture builds")
        .expect("panic fixture emits a native bundle");
    let exact = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation_is_synthesized_whole_function_panic_freedom(
                &function,
                Some("demo"),
                obligation,
            )
        })
        .expect("compiler emits one exact panic identity")
        .clone();

    let expected_function_digest =
        compiler_function_source_digest_hex(&function).expect("function source digest");
    assert_eq!(
        test_obligation_metadata(&exact, TRUST_SOURCE_DIGEST_METADATA_KEY),
        expected_function_digest,
        "the panic aggregate producer and recognizer must share one per-function digest",
    );
    assert_eq!(
        bundle
            .metadata
            .iter()
            .find(|entry| entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY)
            .map(|entry| entry.value.as_str()),
        Some(bundle_source_digest.as_str()),
        "native bundle must retain its separate extract-time source identity",
    );
    assert_ne!(
        bundle_source_digest, expected_function_digest,
        "the regression fixture must distinguish extract-time and current function identities",
    );
    let mut bundle_digest_lookalike = exact.clone();
    bundle_digest_lookalike
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY)
        .expect("panic source digest")
        .value = bundle_source_digest;
    assert!(
        !obligation_is_synthesized_whole_function_panic_freedom(
            &function,
            Some("demo"),
            &bundle_digest_lookalike,
        ),
        "a bundle-level extract-time digest must not substitute for current function authority",
    );

    let mut wrong_id = exact.clone();
    wrong_id.obligation_id.push_str(":lookalike");
    assert!(!obligation_is_synthesized_whole_function_panic_freedom(
        &function,
        Some("demo"),
        &wrong_id,
    ));

    let mut duplicate = exact;
    duplicate.metadata.push(trust_verifier_api::MetadataEntry {
        key: super::TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY.to_string(),
        value: "enabled".to_string(),
    });
    assert!(
        !obligation_is_synthesized_whole_function_panic_freedom(
            &function,
            Some("demo"),
            &duplicate,
        ),
        "duplicate diagnostic markers must not authorize special public/legacy handling"
    );

    let exact = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation_is_synthesized_whole_function_panic_freedom(
                &function,
                Some("demo"),
                obligation,
            )
        })
        .expect("exact panic carrier remains present")
        .clone();
    for mismatch in ["foreign-crate", "foreign-path", "source", "source-digest", "extra-metadata"] {
        let mut forged = exact.clone();
        match mismatch {
            "foreign-crate" | "foreign-path" => {
                mutate_test_obligation_context(&mut forged, |context| {
                    let function = context.function.as_mut().expect("function context");
                    if mismatch == "foreign-crate" {
                        function.crate_name = "attacker".to_string();
                    } else {
                        function.path = "attacker::panic_branch".to_string();
                    }
                });
            }
            "source" => forged.source.line = Some(999),
            "source-digest" => {
                forged
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY)
                    .expect("source digest")
                    .value = "a".repeat(64);
            }
            "extra-metadata" => forged.metadata.push(trust_verifier_api::MetadataEntry {
                key: "attacker.extra".to_string(),
                value: "forged".to_string(),
            }),
            _ => unreachable!(),
        }
        assert!(
            !obligation_is_synthesized_whole_function_panic_freedom(
                &function,
                Some("demo"),
                &forged,
            ),
            "panic identity mismatch `{mismatch}` must fail closed",
        );
    }
}

#[test]
fn assumed_total_marker_requires_exact_compiler_panic_provenance() {
    let function = native_trust_ir_panic_function(true);
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-assumed-total-identity",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
        .expect("panic fixture builds")
        .expect("panic fixture emits a native bundle");
    let exact_index = bundle
        .obligations
        .iter()
        .position(|obligation| {
            obligation_is_synthesized_whole_function_panic_freedom(
                &function,
                Some("demo"),
                obligation,
            )
        })
        .expect("compiler emits one exact panic identity");
    let mut exact = bundle.obligations[exact_index].clone();
    exact.description = format!(
        "{} indirect call `demo::audited` may panic",
        trust_types::assumption::ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX,
    );
    let mut exact_bundle = bundle.clone();
    exact_bundle.obligations[exact_index] = exact.clone();

    assert!(api_obligation_is_assumed_total_callee_marker(&function, &exact_bundle, &exact,));
    assert!(
        !full_verification_dispatched_obligations_for_function(
            &function,
            &exact_bundle,
            &ExactDefinitionEntryMarkerSet::default(),
        )
        .iter()
        .any(|obligation| obligation.obligation_id == exact.obligation_id),
        "only the exact live compiler carrier is removed from proof dispatch",
    );
    assert!(matches!(
        legacy_result_without_native_rows_with_assumed_total(&exact, true),
        VerificationResult::Proved { solver, .. }
            if solver.as_str() == TRUST_ASSUMED_TOTAL_SOLVER
    ));
    let vc = legacy_vc_from_api_obligation(&function, &exact);
    assert!(
        result_obligation_binding_with_compiler_assumptions(0, &vc, &exact, false, true)
            .is_some_and(|binding| binding.assumed_total_callee_assumption),
        "the exact compiler-held carrier may mint only the private assumption classification",
    );

    let mut attacks = Vec::new();

    let mut embedded = exact.clone();
    embedded.description = format!("user text before {}", embedded.description);
    attacks.push(("embedded marker", embedded));

    let mut empty_detail = exact.clone();
    empty_detail.description =
        trust_types::assumption::ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX.to_string();
    attacks.push(("empty marker detail", empty_detail));

    let mut wrong_id = exact.clone();
    wrong_id.obligation_id.push_str(":forged");
    attacks.push(("wrong obligation id", wrong_id));

    let mut wrong_source = exact.clone();
    wrong_source.source.line = Some(wrong_source.source.line.unwrap_or_default() + 1);
    attacks.push(("wrong source", wrong_source));

    let mut wrong_kind = exact.clone();
    wrong_kind.kind = trust_verifier_api::ObligationKind::TemporalSafety;
    attacks.push(("wrong kind", wrong_kind));

    let mut wrong_origin = exact.clone();
    mutate_test_obligation_context(&mut wrong_origin, |context| {
        let trust_verifier_api::ObligationOrigin::VerificationCondition { vc_kind, .. } =
            &mut context.origin
        else {
            panic!("panic fixture context")
        };
        *vc_kind = "bounds_check".to_string();
    });
    attacks.push(("wrong origin", wrong_origin));

    let mut wrong_index = exact.clone();
    mutate_test_obligation_context(&mut wrong_index, |context| {
        let trust_verifier_api::ObligationOrigin::VerificationCondition { vc_index, .. } =
            &mut context.origin
        else {
            panic!("panic fixture context")
        };
        *vc_index = 1;
    });
    attacks.push(("wrong VC index", wrong_index));

    let mut wrong_schema = exact.clone();
    mutate_test_obligation_context(&mut wrong_schema, |context| {
        let trust_verifier_api::ObligationOrigin::VerificationCondition { formula_schema, .. } =
            &mut context.origin
        else {
            panic!("panic fixture context")
        };
        *formula_schema = Some("attacker.formula.v1".to_string());
    });
    attacks.push(("formula schema", wrong_schema));

    let mut wrong_producer = exact.clone();
    mutate_test_obligation_context(&mut wrong_producer, |context| {
        context.producer = trust_verifier_api::ObligationProducer::Compatibility;
    });
    attacks.push(("wrong producer", wrong_producer));

    let mut foreign_function = exact.clone();
    mutate_test_obligation_context(&mut foreign_function, |context| {
        let function = context.function.as_mut().expect("panic fixture function context");
        function.crate_name = "attacker".to_string();
        function.path = "attacker::forged".to_string();
    });
    attacks.push(("foreign function context", foreign_function));

    let mut duplicate_context = exact.clone();
    let context = duplicate_context
        .metadata
        .iter()
        .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
        .expect("panic fixture context metadata")
        .clone();
    duplicate_context.metadata.push(context);
    attacks.push(("duplicate context", duplicate_context));

    let mut missing_stamp = exact.clone();
    missing_stamp
        .metadata
        .retain(|entry| entry.key != TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY);
    attacks.push(("missing panic stamp", missing_stamp));

    let mut duplicate_stamp = exact.clone();
    duplicate_stamp.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY.to_string(),
        value: "enabled".to_string(),
    });
    attacks.push(("duplicate panic stamp", duplicate_stamp));

    let mut invalid_digest = exact.clone();
    invalid_digest
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_VC_DIGEST_METADATA_KEY)
        .expect("VC digest")
        .value = "not-a-digest".to_string();
    attacks.push(("invalid digest", invalid_digest));

    for (name, key) in [
        ("canonical wrong source digest", TRUST_SOURCE_DIGEST_METADATA_KEY),
        ("canonical wrong VC digest", TRUST_VC_DIGEST_METADATA_KEY),
    ] {
        let mut forged = exact.clone();
        let value = &mut forged
            .metadata
            .iter_mut()
            .find(|entry| entry.key == key)
            .expect("digest metadata")
            .value;
        let replacement = if value.starts_with('0') { '1' } else { '0' };
        value.replace_range(..1, &replacement.to_string());
        assert!(canonical_sha256_hex_segment(value));
        attacks.push((name, forged));
    }

    let mut extra_metadata = exact.clone();
    extra_metadata.metadata.push(trust_verifier_api::MetadataEntry {
        key: "attacker.extra".to_string(),
        value: "forged".to_string(),
    });
    attacks.push(("extra metadata", extra_metadata));

    for (name, subject) in [
        (
            "foreign bundle crate",
            trust_verifier_api::BundleSubject::Function {
                crate_name: "attacker".to_string(),
                path: function.def_path.clone(),
            },
        ),
        (
            "foreign bundle path",
            trust_verifier_api::BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::other".to_string(),
            },
        ),
    ] {
        let mut foreign_bundle = exact_bundle.clone();
        foreign_bundle.subject = subject;
        assert!(
            !api_obligation_is_assumed_total_callee_marker(&function, &foreign_bundle, &exact,),
            "{name} must not authenticate the marker",
        );
        assert!(
            full_verification_dispatched_obligations_for_function(
                &function,
                &foreign_bundle,
                &ExactDefinitionEntryMarkerSet::default(),
            )
            .iter()
            .any(|obligation| obligation.obligation_id == exact.obligation_id),
            "{name} must leave the marker in proof dispatch",
        );
    }

    for (name, attack) in attacks {
        let mut attack_bundle = exact_bundle.clone();
        attack_bundle.obligations[exact_index] = attack.clone();
        let authenticated =
            api_obligation_is_assumed_total_callee_marker(&function, &attack_bundle, &attack);
        assert!(!authenticated, "{name} must not classify as an assumed-total compiler marker",);
        assert!(
            full_verification_dispatched_obligations_for_function(
                &function,
                &attack_bundle,
                &ExactDefinitionEntryMarkerSet::default(),
            )
            .iter()
            .any(|obligation| obligation.obligation_id == attack.obligation_id),
            "{name} must remain a proof request",
        );
        assert!(
            !matches!(
                legacy_result_without_native_rows_with_assumed_total(&attack, authenticated),
                VerificationResult::Proved { solver, .. }
                    if solver.as_str() == TRUST_ASSUMED_TOTAL_SOLVER
            ),
            "{name} must not skip dispatch through a private Proved bookkeeping row",
        );
        let attack_vc = legacy_vc_from_api_obligation(&function, &attack);
        assert!(
            !result_obligation_binding_with_compiler_assumptions(
                0,
                &attack_vc,
                &attack,
                false,
                authenticated,
            )
            .is_some_and(|binding| binding.assumed_total_callee_assumption),
            "{name} must not mint private assumed-total authority",
        );
    }
}

#[test]
fn synthesized_panic_source_inventory_and_identity_collisions_fail_closed() {
    let function = native_trust_ir_panic_function(true);
    let mut module = trust_ir_bridge::lower_mir_compat_to_trust_ir(&function)
        .expect("panic fixture lowers to TrustIr");
    let inventory: FxHashSet<String> = [function.def_path.clone()].into_iter().collect();
    let empty_bundle = || {
        trust_verifier_api::TrustContractBundle::empty(
            "panic-collision",
            trust_verifier_api::BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: function.def_path.clone(),
            },
        )
    };

    let mut exact = empty_bundle();
    synthesize_native_panic_freedom_to_verifier_api_obligations(
        &function, &mut exact, &module, &inventory,
    )
    .expect("compiler aggregate synthesizes");
    let exact_len = exact.obligations.len();
    synthesize_native_panic_freedom_to_verifier_api_obligations(
        &function, &mut exact, &module, &inventory,
    )
    .expect("an exact pre-annotation compiler row is idempotent");
    assert_eq!(exact.obligations.len(), exact_len);

    let mut collision = empty_bundle();
    let mut forged = exact.obligations[0].clone();
    forged.description = "forged collision".to_string();
    collision.obligations.push(forged);
    assert!(
        synthesize_native_panic_freedom_to_verifier_api_obligations(
            &function,
            &mut collision,
            &module,
            &inventory,
        )
        .is_err(),
        "a different preexisting row must not suppress the counted panic carrier",
    );

    let proof = module
        .proof_obligations
        .iter_mut()
        .find(|proof| proof.kind == trust_ir::ObligationKind::PanicFreedom)
        .expect("panic aggregate proof row");
    let formula = proof.formula.as_mut().expect("panic aggregate source payload");
    let mut payload: serde_json::Value =
        serde_json::from_str(&formula.payload).expect("panic source JSON");
    payload["source_id"] =
        serde_json::Value::String("mir-assertions:attacker::foreign:panic-freedom".to_string());
    formula.payload = serde_json::to_string(&payload).expect("mutated panic source JSON");
    let mut foreign = empty_bundle();
    assert!(
        synthesize_native_panic_freedom_to_verifier_api_obligations(
            &function,
            &mut foreign,
            &module,
            &inventory,
        )
        .is_err(),
        "a foreign function-level source must not mint the target aggregate",
    );
}

#[test]
fn trust_mc_default_function_chc_routing_rejects_marker_lookalikes_and_duplicates() {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-default-routing-identity",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
        .expect("native TrustIr bundle builds")
        .expect("default admission creates a native request");
    let exact = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.is_default_admission())
        .expect("compiler emits one exact admission")
        .clone();
    assert!(trust_mc_routes_to_structural_default_function_chc(&exact, true));
    assert!(!trust_mc_routes_to_structural_default_function_chc(&exact, false));

    let mut lookalike = exact.clone();
    lookalike
        .metadata
        .iter_mut()
        .find(|entry| {
            entry.key == trust_verifier_api::TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY
        })
        .expect("marker exists")
        .value = "enabled".to_string();
    assert!(!lookalike.is_default_admission());
    assert!(
        !trust_mc_routes_to_structural_default_function_chc(&lookalike, true),
        "a presence-only marker lookalike must stay on semantic CHC lowering"
    );

    let mut duplicate = exact;
    duplicate.metadata.push(trust_verifier_api::MetadataEntry {
        key: trust_verifier_api::TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY.to_string(),
        value: trust_verifier_api::TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE.to_string(),
    });
    assert!(!duplicate.is_default_admission());
    assert!(
        !trust_mc_routes_to_structural_default_function_chc(&duplicate, true),
        "duplicate public marker keys must not select the vacuous structural route"
    );
}

#[test]
fn native_trust_ir_function_binding_rejects_name_mismatch_without_first_function_fallback() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let mut module = trust_ir::Module::new("demo");
    let ty = module.add_func_type(trust_ir::FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: false,
    });
    module.add_function(trust_ir::Function::new(
        trust_ir::FuncId::new(0),
        "demo::unrelated",
        ty,
        trust_ir::BlockId::new(0),
    ));

    let err = native_trust_ir_function_id(&module, &function)
        .expect_err("native TrustIr binding must not silently choose the first function");

    assert!(err.contains("did not produce a matching function"), "{err}");
    assert!(err.contains("demo::checked_transfer"), "{err}");
    assert!(err.contains("demo::unrelated"), "{err}");
}

#[test]
fn trust_mc_unsupported_typed_chc_lowering_emits_blocker_metadata_not_absence() {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();
    let unsupported_obligation_id = "vc:demo:assertion:unsupported-typed-chc";
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-unsupported-trust-mc",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: unsupported_obligation_id.to_string(),
        kind: trust_verifier_api::ObligationKind::Assertion,
        contract_id: None,
        proof_item_id: None,
        source: native_trust_ir_test_source_location(23),
        description: "assertion without typed formula metadata".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: "33".repeat(32),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: "44".repeat(32),
            },
        ],
    });

    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
            .expect("native TrustIr bundle should build")
            .expect("unsupported trust-mc lowering should still emit a native TrustIr request");

    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == unsupported_obligation_id)
        .expect("unsupported trust-mc obligation should remain public");
    assert_native_proof_unit_metadata(obligation, "trust-mc");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY
        ),
        "unsupported"
    );
    let unsupported_reason = test_obligation_metadata(
        obligation,
        super::TRUST_MC_TYPED_CHC_UNSUPPORTED_REASON_METADATA_KEY,
    );
    assert!(unsupported_reason.contains(TRUST_VC_FORMULA_SCHEMA_METADATA_KEY));
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY
        ),
        "unsupported"
    );
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_UNSUPPORTED_REASON_METADATA_KEY
        ),
        unsupported_reason
    );

    let trust_mc_contract_id = test_obligation_metadata(
        obligation,
        super::TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY,
    );
    let trust_mc_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == trust_mc_contract_id)
        .expect("unsupported lowering should still append a typed CHC contract");
    let trust_verifier_api::ContractPredicate::MathIr { value, .. } = &trust_mc_contract.predicate
    else {
        panic!("unsupported trust-mc contract must be MathIr");
    };
    assert_eq!(value["unsupported"]["status"], "unsupported");
    assert_eq!(value["unsupported"]["reason"], unsupported_reason);
    assert_eq!(value["trust_native_admission"]["unsupported_semantics_status"], "unsupported");
    assert_eq!(value["rules"][0]["body"]["constraints"][0]["value"], false);

    let proof_obligation_id = test_obligation_metadata(
        obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .parse::<u32>()
    .map(trust_ir::ProofId::new)
    .expect("proof obligation id should parse");
    let trust_mc_request = native_trust_ir_bundle
        .requests
        .iter()
        .find(|request| {
            matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustMc)
                && request.obligations().contains(&proof_obligation_id)
        })
        .expect("unsupported trust-mc obligation should have its own native request");
    let trust_ir::NativeVerificationRequest::TrustMc(trust_mc_request) = trust_mc_request else {
        panic!("request should be trust-mc");
    };
    assert!(
        trust_mc_request
            .provenance
            .replay_context
            .atoms
            .iter()
            .any(|atom| atom.obligation == Some(proof_obligation_id)),
        "unsupported lowering should still have a typed native request/replay atom"
    );
}

#[test]
fn full_verification_compiler_input_defers_direct_trust_vc_proof_unit() {
    let (function, compiler_contracts, vcs) = native_trust_ir_compiler_function();
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("postcondition and arithmetic-safety obligations require native TrustIr");

    assert_eq!(bundle.obligations.len(), 4);
    assert!(
        bundle
            .obligations
            .iter()
            .all(|obligation| !obligation.obligation_id.starts_with("trust_ir-native-"))
    );

    let public_native_obligation_ids = bundle
        .obligations
        .iter()
        .filter(|obligation| {
            obligation.metadata.iter().any(|entry| {
                entry.key
                    == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
            })
        })
        .map(|obligation| obligation.obligation_id.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let compiler_fact_public_obligation_ids = native_trust_ir_bundle
        .compiler_facts
        .obligation_sources
        .iter()
        .map(|source| source.public_obligation_id.clone())
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        native_trust_ir_bundle
            .compiler_facts
            .obligation_sources
            .iter()
            .all(|source| !source.public_obligation_id.is_empty()),
        "every native compiler fact must identify its exact public verifier obligation"
    );
    assert_eq!(
        native_trust_ir_bundle.compiler_facts.obligation_sources.len(),
        compiler_fact_public_obligation_ids.len(),
        "native proof rows must not alias one public verifier obligation"
    );
    assert_eq!(
        native_trust_ir_bundle.module.proof_obligations.len(),
        compiler_fact_public_obligation_ids.len(),
        "bridge-local proof rows must not survive the public inventory boundary"
    );
    assert_eq!(
        compiler_fact_public_obligation_ids, public_native_obligation_ids,
        "the module proof inventory must exactly match the routed public verifier inventory"
    );

    let request_suites = native_trust_ir_bundle
        .requests
        .iter()
        .map(|request| native_verifier_suite_canonical_label(request.verifier_suite()))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        request_suites,
        ["trust-wp".to_string(), "trust-mc".to_string()].into_iter().collect()
    );
    assert!(
        native_trust_ir_bundle.module.proof_certificates.is_empty(),
        "a structured direct trust-vc carrier must not mint a native certificate before the deadline-aware verifier runs"
    );
    let trust_vc_public_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::Ownership)
        .expect("trust-vc ownership obligation should be present");
    assert_eq!(
        trust_vc_bridge::trust_vc_validate_structured_direct_mir_memory_obligation_metadata(
            trust_vc_public_obligation,
        ),
        Ok(true),
        "the compiler producer and direct TrustVC carrier validator must agree on the exact canonical payload"
    );
    assert!(trust_vc_public_obligation.metadata.iter().all(|entry| {
        entry.key
            != trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
    }));
    assert_eq!(
        test_obligation_metadata(
            trust_vc_public_obligation,
            TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY,
        ),
        trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED
    );
    assert_eq!(
        test_obligation_metadata(
            trust_vc_public_obligation,
            TRUST_TRUST_IR_NATIVE_UNSUPPORTED_REASON_METADATA_KEY,
        ),
        trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON,
    );
    assert!(!trust_vc_public_obligation.metadata.iter().any(|entry| {
        entry.key
            == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
            || entry.key
                == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
    }));

    for (suite, kind) in [
        ("trust-wp", trust_verifier_api::ObligationKind::Postcondition),
        ("trust-mc", trust_verifier_api::ObligationKind::ArithmeticSafety),
    ] {
        let obligation = bundle
            .obligations
            .iter()
            .find(|obligation| obligation.kind == kind)
            .expect("suite obligation should be present");
        assert!(obligation.metadata.iter().any(|entry| {
            entry.key
                == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                && entry.value == suite
        }));
        assert!(obligation.metadata.iter().any(|entry| {
            entry.key == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
        }));
        assert!(obligation.metadata.iter().any(|entry| {
            entry.key
                == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
        }));
        assert_native_proof_unit_metadata(obligation, suite);
    }
    let trust_wp_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::Postcondition)
        .expect("trust-wp postcondition obligation should be present");
    let has_trust_wp_replay_metadata =
        trust_router::full_verification::TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS
            .iter()
            .all(|key| trust_wp_obligation.metadata.iter().any(|entry| entry.key == *key));
    if has_trust_wp_replay_metadata {
        let native_origin = test_obligation_metadata_json(
            trust_wp_obligation,
            trust_router::full_verification::TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
        );
        // Wire-format pin: trust-wp-core's strict native-origin validation
        // (placeholder-solver rejection, proof-context atom binding, lineage
        // and digest requirements) is fail-closed ONLY for schema names under
        // the canonical `tmir.native-verification-bundle.` prefix (see
        // trust-wp-core `verify_bundle::types`). Emitting any other spelling
        // (e.g. a blanket-renamed `trust_ir.` form) silently disables those
        // checks downstream, so this pin must track the first-party canonical
        // spelling.
        assert_eq!(
            native_origin["schema"],
            format!(
                "tmir.native-verification-bundle.v{}",
                trust_ir_bridge::NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION
            )
        );
        assert_eq!(native_origin["mode"], "weakest_precondition");
        assert_eq!(
            native_origin["obligation_id"].as_u64(),
            trust_wp_obligation
                .metadata
                .iter()
                .find(|entry| {
                    entry.key
                        == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
                })
                .and_then(|entry| entry.value.parse::<u64>().ok())
        );
        let native_replay = test_obligation_metadata_json(
            trust_wp_obligation,
            trust_router::full_verification::TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
        );
        assert_eq!(native_replay["engine"], "trust-wp-core.native-pure-replay");
        assert!(native_replay["transcript_digest"]["value"].as_str().is_some());
        let obligation_source = test_obligation_metadata_json(
            trust_wp_obligation,
            trust_router::full_verification::TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY,
        );
        assert_eq!(obligation_source["cause"], "postcondition");
        let proof_context = test_obligation_metadata_json(
            trust_wp_obligation,
            trust_router::full_verification::TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
        );
        let proof_context_assertions = proof_context["assertions"]
            .as_array()
            .expect("trust-wp proof context should contain assertions");
        assert_eq!(proof_context["assumptions"].as_array().map(Vec::len), Some(0));
        assert_eq!(
            proof_context_assertions.first().and_then(|atom| atom["index"].as_u64()),
            Some(0)
        );
        assert_eq!(
            proof_context_assertions
                .first()
                .and_then(|atom| atom.pointer("/claim/format"))
                .and_then(|value| value.as_str()),
            Some("trust_formula_v1")
        );
        let proof_context_payload = proof_context_assertions
            .first()
            .and_then(|atom| atom.pointer("/claim/payload"))
            .and_then(|value| value.as_str())
            .expect("trust-wp proof-context assertion should carry a typed payload");
        let proof_context_payload: serde_json::Value = serde_json::from_str(proof_context_payload)
            .expect("TrustFormulaV1 payload should parse");
        assert_eq!(proof_context_payload["schema"], "trust_wp.trust-formula.v1");
        assert_eq!(proof_context_payload["body"]["bool"], true);
    }
    let trust_mc_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::ArithmeticSafety)
        .expect("trust-mc arithmetic-safety obligation should be present");
    let trust_mc_public_contract_id = trust_mc_obligation
        .contract_id
        .as_deref()
        .expect("supported trust-mc lowering must link its canonical public semantic contract");
    let trust_mc_public_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == trust_mc_public_contract_id)
        .expect("canonical trust-mc public contract should be in the verifier bundle");
    let trust_verifier_api::ContractPredicate::MathIr {
        schema: public_schema,
        value: public_value,
    } = &trust_mc_public_contract.predicate
    else {
        panic!("canonical trust-mc public contract must be MathIr");
    };
    assert_eq!(public_schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(public_value["obligation_id"], trust_mc_obligation.obligation_id);
    assert!(public_value.get("native_metadata").is_none());

    let trust_mc_contract_id = test_obligation_metadata(
        trust_mc_obligation,
        super::TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY,
    );
    assert_ne!(trust_mc_contract_id, trust_mc_public_contract_id);
    let trust_mc_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == trust_mc_contract_id)
        .expect("typed trust-mc synthetic contract should be in the verifier bundle");
    let trust_verifier_api::ContractPredicate::MathIr { schema, value } =
        &trust_mc_contract.predicate
    else {
        panic!("typed trust-mc contract must be MathIr");
    };
    assert_eq!(schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["schema_version"], super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["origin"], "mir_derived");
    assert_eq!(value["query"]["target"], "error");
    assert_eq!(value["relations"], serde_json::json!([{ "name": "error" }]));
    assert_eq!(value["vars"], serde_json::json!([{ "name": "amount", "sort": { "kind": "int" } }]));
    assert_eq!(value["rules"][0]["head"]["name"], "error");
    let trust_mc_constraint = &value["rules"][0]["body"]["constraints"][0];
    assert_eq!(trust_mc_constraint["kind"], "binary");
    assert_eq!(trust_mc_constraint["op"], "and");
    assert_eq!(trust_mc_constraint["lhs"]["op"], "ge");
    assert_eq!(trust_mc_constraint["rhs"]["op"], "lt");
    assert!(
        value["obligation_id"]
            .as_str()
            .is_some_and(|id| id.starts_with("trust_ir-native-trust_mc-request-"))
    );
    assert_eq!(value["native_metadata"]["producer"], "TrustIr");
    assert_eq!(value["native_metadata"]["adapter_input"], "rust-mir");
    assert_eq!(value["native_metadata"]["verification_mode"], "chc");
    assert_eq!(
        value["native_metadata"]["native_request_id"].as_u64(),
        trust_mc_obligation
            .metadata
            .iter()
            .find(|entry| {
                entry.key
                    == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
            })
            .and_then(|entry| entry.value.parse::<u64>().ok())
    );
    assert_eq!(
        value["native_metadata"]["proof_obligation_ids"]
            .as_array()
            .and_then(|ids| ids.first())
            .and_then(|id| id.as_u64()),
        trust_mc_obligation
            .metadata
            .iter()
            .find(|entry| {
                entry.key
                    == trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
            })
            .and_then(|entry| entry.value.parse::<u64>().ok())
    );
    assert!(
        value["native_metadata"]["compiler_fact_sources"]
            .as_array()
            .is_some_and(|sources| !sources.is_empty()),
        "typed trust-mc input must bind native compiler fact sources"
    );
    assert!(
        value["native_metadata"]["replay_context"]["atoms"]
            .as_array()
            .is_some_and(|atoms| !atoms.is_empty()),
        "typed trust-mc input must carry native replay atoms"
    );
    let trust_mc_proof_obligation_id = test_obligation_metadata(
        trust_mc_obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .parse::<u32>()
    .map(trust_ir::ProofId::new)
    .expect("trust-mc proof obligation id should parse");
    let trust_mc_request = native_trust_ir_bundle
        .requests
        .iter()
        .find(|request| matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustMc))
        .expect("native bundle should include a trust-mc request");
    let trust_ir::NativeVerificationRequest::TrustMc(trust_mc_request) = trust_mc_request else {
        panic!("trust-mc request should have the trust-mc variant");
    };
    let trust_mc_replay_atom = trust_mc_request
        .provenance
        .replay_context
        .atoms
        .iter()
        .find(|atom| {
            atom.kind == trust_ir::NativeReplayAtomKind::Assertion
                && atom.obligation == Some(trust_mc_proof_obligation_id)
        })
        .expect("trust-mc replay context should bind the compiler proof obligation");
    assert_eq!(
        trust_mc_replay_atom.formula.schema,
        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION
    );
    assert_eq!(trust_mc_replay_atom.payload_digest, trust_mc_replay_atom.expected_payload_digest());
    assert_eq!(
        trust_mc_contract
            .metadata
            .iter()
            .find(|entry| entry.key == "trust-trust-mc.typed-chc-obligation.source")
            .map(|entry| entry.value.as_str()),
        Some("compiler-native-trust-ir-trust-spec-vc")
    );
    let trust_mc_binding = trust_mc_contract
        .metadata
        .iter()
        .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY)
        .map(|entry| entry.value.as_str())
        .expect("typed trust-mc contract should carry binding metadata");
    let trust_mc_binding: serde_json::Value =
        serde_json::from_str(trust_mc_binding).expect("binding metadata should parse");
    let trust_mc_source_digest = trust_mc_contract
        .metadata
        .iter()
        .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY)
        .map(|entry| entry.value.as_str())
        .expect("typed trust-mc contract should carry source digest");
    let trust_mc_synthetic_digest = trust_mc_contract
        .metadata
        .iter()
        .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY)
        .map(|entry| entry.value.as_str())
        .expect("typed trust-mc contract should carry synthetic digest");
    assert_eq!(trust_mc_source_digest.len(), 64);
    assert_eq!(trust_mc_synthetic_digest.len(), 64);
    assert_eq!(trust_mc_binding["source_digest"]["value"].as_str(), Some(trust_mc_source_digest));
    assert_eq!(
        trust_mc_binding["synthetic_chc_digest"]["value"].as_str(),
        Some(trust_mc_synthetic_digest)
    );
    assert_eq!(
        test_obligation_metadata(
            trust_mc_obligation,
            super::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY,
        ),
        trust_mc_contract
            .metadata
            .iter()
            .find(|entry| entry.key == super::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY)
            .map(|entry| entry.value.as_str())
            .expect("contract binding metadata")
    );
    let calls = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let engine = trust_router::FullVerificationEngine::new(
        vec![
            Box::new(NativeTrustIrUnitEngine::new(
                "trust-wp",
                trust_verifier_api::EngineKind::Deductive,
                trust_verifier_api::ObligationKind::Postcondition,
                trust_verifier_api::ProofStrength::deductive(),
                vec![
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                        "trust-wp-solver-transcript",
                    ),
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::ProofCheckReport,
                        "trust-wp-proof-check",
                    ),
                ],
                calls.clone(),
            )),
            Box::new(NativeTrustIrUnitEngine::new(
                "trust-mc",
                trust_verifier_api::EngineKind::Reachability,
                trust_verifier_api::ObligationKind::ArithmeticSafety,
                trust_verifier_api::ProofStrength {
                    reasoning: trust_verifier_api::ReasoningKind::Pdr,
                    assurance: trust_verifier_api::AssuranceLevel::SmtBacked,
                },
                vec![
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                        "trust-mc-solver-transcript",
                    ),
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::ProofCheckReport,
                        "trust-mc-proof-check",
                    ),
                ],
                calls.clone(),
            )),
            Box::new(NativeTrustIrUnitEngine::new(
                "trust-vc",
                trust_verifier_api::EngineKind::Deductive,
                trust_verifier_api::ObligationKind::Ownership,
                trust_verifier_api::ProofStrength::certified(
                    trust_verifier_api::ReasoningKind::OwnershipAnalysis,
                ),
                vec![trust_vc_native_trust_ir_test_proof_certificate_artifact(
                    "trust-vc-proof-certificate",
                )],
                calls.clone(),
            )),
        ],
        trust_router::FullVerificationPolicy {
            require_all_required_engines: false,
            ..trust_router::FullVerificationPolicy::default()
        },
    );

    let result = verify_full_bundle_with_optional_native_trust_ir(
        &engine,
        &bundle,
        &bundle.obligations,
        Some(&native_trust_ir_bundle),
        &trust_router::VerifierExecutionContext::new("trustc-native-trust-ir-test"),
    );

    assert_eq!(
        result.status,
        trust_verifier_api::VerificationRunStatus::Proved,
        "the release-admissible direct TrustVC unit must be accepted by the public verifier run: {result:#?}"
    );
    // The trivially-true `ensures "true"` row remains an admission. All three
    // requested rows are release-grade public evidence; the compiler still
    // requires the private affine receipt below before that public TrustVC
    // attribution can authorize a static `proved` transport row.
    assert_eq!(result.summary.proved, 3);
    assert_eq!(result.summary.admitted, 1);
    assert_eq!(
        result.summary.missing_proof_artifacts, 0,
        "unsupported evidence is not a proved row missing artifacts"
    );
    let trust_vc_structured = result
        .full_verification_obligation_evidence()
        .into_iter()
        .find(|item| item.obligation_id == trust_vc_public_obligation.obligation_id)
        .expect("accepted trust-vc evidence must retain a structured evidence view");
    assert!(trust_vc_structured.has_accepted_proof());
    assert!(trust_vc_structured.blockers.is_empty());
    let mut called = calls.lock().expect("native test engine calls lock").clone();
    called.sort();
    assert_eq!(
        called,
        vec!["trust-mc".to_string(), "trust-wp".to_string()],
        "direct TrustVC dispatch is handled by its dedicated verifier path, not the native test-engine fallback"
    );

    for suite in ["trust-wp", "trust-mc"] {
        let evidence = result
            .evidence
            .iter()
            .find(|evidence| {
                evidence
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(&format!("suite={suite}")))
            })
            .expect("accepted native TrustIr evidence should carry suite diagnostic");
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("typed TrustIr native request identity accepted")
        }));
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::EngineInput
                && artifact.uri.contains(&format!("/{suite}/request/"))
        }));
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::NormalizedObligation
                && artifact.uri.contains("/proof/")
        }));
    }
    let trust_vc_evidence = result
        .evidence
        .iter()
        .find(|evidence| evidence.obligation_id == trust_vc_public_obligation.obligation_id)
        .expect("accepted direct trust-vc evidence should be retained");
    assert_eq!(trust_vc_evidence.status, trust_verifier_api::EvidenceStatus::Proved);
    assert_eq!(
        trust_vc_evidence.proof_strength.as_ref(),
        Some(&trust_verifier_api::ProofStrength::certified(
            trust_verifier_api::ReasoningKind::OwnershipAnalysis,
        )),
    );
    assert!(
        trust_vc_evidence.artifacts.iter().any(|artifact| artifact.kind
            == trust_verifier_api::EvidenceArtifactKind::ProofCertificate
            && artifact.materialization.is_some()),
        "the accepted import must retain its materialized release-grade proof certificate: {trust_vc_evidence:#?}"
    );

    let transport_results =
        bound_full_transport_results_for_test(true, &function, &bundle, &result);
    let message =
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            function: function.def_path.clone(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            proved: transport_results.iter().filter(|row| row.outcome == Outcome::Proved).count(),
            failed: transport_results.iter().filter(|row| row.outcome == Outcome::Failed).count(),
            unknown: transport_results.iter().filter(|row| row.outcome == Outcome::Unknown).count(),
            timed_out: transport_results
                .iter()
                .filter(|row| row.outcome.is_timeout())
                .count(),
            skipped: transport_results.iter().filter(|row| row.outcome == Outcome::Skipped).count(),
            runtime_checked: transport_results
                .iter()
                .filter(|row| row.outcome == Outcome::RuntimeChecked)
                .count(),
            cached: 0,
            total: transport_results.len(),
            results: transport_results,
        });
    let transport_json =
        serde_json::to_value(message).expect("transport message should serialize as JSON");
    let rows = transport_json
        .get("results")
        .and_then(|value| value.as_array())
        .expect("emitted function transport JSON should contain result rows");

    let trust_vc_row = rows
        .iter()
        .find(|row| {
            row.get("obligation_id").and_then(|value| value.as_str())
                == Some(trust_vc_public_obligation.obligation_id.as_str())
        })
        .expect("the accepted trust-vc obligation must retain a structured transport row");
    assert_eq!(
        trust_vc_row.get("outcome").and_then(|value| value.as_str()),
        Some("unknown"),
        "serializable public evidence alone must not mint the compiler's affine TrustVC authority"
    );
    let native = trust_vc_row
        .get("native_trust_ir")
        .expect("the deferred direct trust-vc carrier must retain native diagnostics");
    assert_eq!(
        native.get("suite").and_then(|value| value.as_str()),
        Some("trust-full-verifier"),
        "an identity-free direct carrier reports the composite evidence owner, not a forged native request identity"
    );
    assert_eq!(native.get("present").and_then(|value| value.as_bool()), Some(false));
    assert!(native.get("request_id").is_none());
    assert!(native.get("native_id").is_none());
    assert!(
        native["diagnostics"]
            .as_array()
            .expect("deferred direct-carrier diagnostics should serialize")
            .iter()
            .any(|diagnostic| diagnostic["message"]
                .as_str()
                .is_some_and(|message| message
                    == trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON))
    );
    assert!(
        trust_vc_row.get("proof_evidence").is_none_or(serde_json::Value::is_null),
        "accepted public proof bytes remain attribution-only until the private live receipt is consumed"
    );
}

/// Adding the E4/E5 rows must be monotone over the already-required per-site
/// safety obligation set. A non-empty solver VC vector must not let incidental
/// loop rows hide an independently-discovered allocation obligation.
#[test]
fn loop_vcs_do_not_suppress_unbounded_allocation_obligations() {
    let (mut function, compiler_contracts, _) = native_trust_ir_compiler_function();
    function.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: Vec::new(),
        terminator: trust_types::Terminator::Return,
    }];

    let vc = |kind, line| VerificationCondition {
        kind,
        function: trust_types::Symbol::intern("demo::checked_transfer"),
        location: native_trust_ir_test_span(line),
        // A false violation formula is enough to exercise routing/binding.
        formula: trust_types::Formula::Bool(false),
        contract_metadata: None,
    };
    let allocation = vc(
        VcKind::UnboundedAllocation {
            callee: "Vec::with_capacity".to_string(),
            count: "n".to_string(),
            detail: "no dominating allocation bound".to_string(),
        },
        21,
    );
    let baseline_vcs = vec![allocation.clone()];
    let mut enriched_vcs = baseline_vcs.clone();
    enriched_vcs.extend([
        vc(
            VcKind::LoopInvariantInitiation { invariant: "i <= n".to_string(), header_block: 1 },
            22,
        ),
        vc(
            VcKind::LoopInvariantConsecution { invariant: "i <= n".to_string(), header_block: 1 },
            23,
        ),
        vc(
            VcKind::NonTermination {
                context: "loop-decreases".to_string(),
                measure: "n - i".to_string(),
            },
            24,
        ),
    ]);

    let (baseline, baseline_native) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &baseline_vcs);
    baseline_native
        .expect("baseline native bundle should build")
        .expect("allocation obligation requires a native request");
    let (enriched, enriched_native) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &enriched_vcs);
    enriched_native
        .expect("loop-enriched native bundle should build")
        .expect("E4/E5 rows require native requests");

    let has_metadata =
        |bundle: &trust_verifier_api::TrustContractBundle, key: &str, value: &str| {
            bundle.obligations.iter().any(|obligation| {
                obligation.metadata.iter().any(|entry| entry.key == key && entry.value == value)
            })
        };
    for bundle in [&baseline, &enriched] {
        assert!(bundle.obligations.iter().any(|obligation| matches!(
            &obligation.kind,
            trust_verifier_api::ObligationKind::Custom { namespace, name }
                if namespace == "trust.vc.unbounded_allocation"
                    && name == "unbounded_allocation"
        )));
    }
    for kind in ["loop_invariant_initiation", "loop_invariant_consecution", "non_termination"] {
        assert!(has_metadata(&enriched, "trust.vc.kind", kind), "missing {kind} row");
    }

    let baseline_ids = baseline
        .obligations
        .iter()
        .map(|obligation| obligation.obligation_id.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    let enriched_ids = enriched
        .obligations
        .iter()
        .map(|obligation| obligation.obligation_id.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        baseline_ids.is_subset(&enriched_ids),
        "adding E4/E5 obligations must not delete or rename existing safety obligations"
    );

    for obligation in enriched.obligations.iter().filter(|obligation| {
        matches!(
            obligation.kind,
            trust_verifier_api::ObligationKind::LoopInvariant
                | trust_verifier_api::ObligationKind::Termination
        )
    }) {
        assert_eq!(
            native_trust_ir_route_for_api_obligation(obligation),
            Some(("trust-mc", trust_ir::ObligationKind::PanicFreedom)),
            "closed E4/E5 violation formula must use the typed CHC/PDR kernel"
        );
        assert!(
            trust_mc_typed_chc_constraint_for_obligation(obligation)
                .expect("typed CHC lowering should be well formed")
                .is_some(),
            "E4/E5 obligation must carry a kernel-consumable typed formula"
        );
    }
}

#[test]
fn partial_or_forged_e4_e5_envelopes_keep_the_legacy_trust_wp_route() {
    let (mut function, compiler_contracts, _) = native_trust_ir_compiler_function();
    function.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: Vec::new(),
        terminator: trust_types::Terminator::Return,
    }];
    let vcs = vec![
        VerificationCondition {
            kind: VcKind::LoopInvariantInitiation {
                invariant: "i <= n".to_string(),
                header_block: 1,
            },
            function: trust_types::Symbol::intern(&function.name),
            location: native_trust_ir_test_span(25),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::NonTermination {
                context: "loop-decreases".to_string(),
                measure: "n - i".to_string(),
            },
            function: trust_types::Symbol::intern(&function.name),
            location: native_trust_ir_test_span(26),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
    ];
    let (bundle, _) = build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);

    for obligation in bundle.obligations.iter().filter(|obligation| {
        matches!(
            obligation.kind,
            trust_verifier_api::ObligationKind::LoopInvariant
                | trust_verifier_api::ObligationKind::Termination
        )
    }) {
        let legacy_route = match obligation.kind {
            trust_verifier_api::ObligationKind::LoopInvariant => {
                ("trust-wp", trust_ir::ObligationKind::LoopInvariant)
            }
            trust_verifier_api::ObligationKind::Termination => {
                ("trust-wp", trust_ir::ObligationKind::TranslationValidation)
            }
            _ => unreachable!(),
        };
        assert_eq!(
            native_trust_ir_route_for_api_obligation(obligation),
            Some(("trust-mc", trust_ir::ObligationKind::PanicFreedom)),
            "fixture must begin with the complete current compiler envelope"
        );

        let mut partial = obligation.clone();
        partial.metadata.retain(|entry| entry.key != TRUST_VC_FORMULA_SCHEMA_METADATA_KEY);
        assert_eq!(
            native_trust_ir_route_for_api_obligation(&partial),
            Some(legacy_route.clone()),
            "a payload without its unique current formula schema must not change ownership"
        );

        let mut ambiguous = obligation.clone();
        let duplicate_payload = ambiguous
            .metadata
            .iter()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("complete compiler payload")
            .clone();
        ambiguous.metadata.push(duplicate_payload);
        assert_eq!(
            native_trust_ir_route_for_api_obligation(&ambiguous),
            Some(legacy_route.clone()),
            "duplicated payload metadata is not a unique compiler envelope"
        );

        let mut structurally_invalid = obligation.clone();
        let undeclared = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::variable(
                "missing",
                trust_verifier_api::TrustSpecSort::Bool,
            ),
            Vec::new(),
        );
        structurally_invalid
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("complete compiler payload")
            .value = serde_json::to_string(&undeclared).expect("invalid fixture serializes");
        assert_eq!(
            native_trust_ir_route_for_api_obligation(&structurally_invalid),
            Some(legacy_route.clone()),
            "schema/root checks alone cannot move a malformed predicate to TrustMC"
        );

        let mut forged_context = obligation.clone();
        forged_context
            .metadata
            .iter_mut()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("complete compiler context")
            .value = "{}".to_string();
        assert_eq!(
            native_trust_ir_route_for_api_obligation(&forged_context),
            Some(legacy_route),
            "an unparsable or forged context must retain TrustWP ownership"
        );
    }
}

struct DirectTrustVcCompilerFixture {
    bundle: trust_verifier_api::TrustContractBundle,
    dispatched: Vec<trust_verifier_api::TrustObligation>,
    context: trust_router::VerifierExecutionContext,
    final_run: trust_verifier_api::VerificationRunResult,
    live_receipts: trust_router::LiveVerificationReceiptBatch,
    results: Vec<(VerificationCondition, VerificationResult)>,
    bindings: Vec<Option<ResultObligationBinding>>,
}

fn direct_trust_vc_live_fixture(run_id: &str) -> DirectTrustVcCompilerFixture {
    let (function, compiler_contracts, vcs) = native_trust_ir_compiler_function();
    let (bundle, native_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_bundle = native_bundle
        .expect("direct TrustVC native bundle planning must succeed")
        .expect("the sibling TrustWP/TrustMC rows require a native bundle");
    let dispatched = full_verification_dispatched_obligations(
        &bundle,
        &ExactDefinitionEntryMarkerSet::default(),
    );
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    let context = trust_router::VerifierExecutionContext::new(run_id).with_deadline(deadline);
    let live = verify_full_bundle_with_body_bound_receipts(
        &bundle,
        &dispatched,
        Some(&native_bundle),
        &[],
        &context,
    );
    assert!(live.body_bound_receipts.is_empty());
    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &vcs,
        live.result.context.clone(),
    );
    let (results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &live.result,
        &vcs,
        &snapshot,
    );
    let live_receipts = live.live_receipts.expect("live receipt package");
    DirectTrustVcCompilerFixture {
        bundle,
        dispatched,
        context,
        final_run: live.result,
        live_receipts,
        results,
        bindings,
    }
}

fn direct_trust_vc_fixture_row(
    fixture: &DirectTrustVcCompilerFixture,
    public_obligation_id: &str,
) -> usize {
    fixture
        .bindings
        .iter()
        .position(|binding| {
            binding
                .as_ref()
                .is_some_and(|binding| binding.public_obligation_id == public_obligation_id)
        })
        .expect("direct TrustVC receipt must retain one exact compiler row binding")
}

#[test]
fn direct_trust_vc_live_receipt_is_exact_ownership_authority_and_public_run_is_not() {
    let DirectTrustVcCompilerFixture {
        bundle,
        dispatched,
        context,
        final_run,
        mut live_receipts,
        results,
        bindings,
    } = direct_trust_vc_live_fixture("compiler-direct-trust-vc-live");
    assert_eq!(
        live_receipts.direct_trust_vc_receipts().len(),
        1,
        "one Ownership row must retain a live receipt: {final_run:#?}"
    );
    let receipt_id =
        live_receipts.direct_trust_vc_receipts().keys().next().expect("one direct receipt").clone();
    let target_row = bindings
        .iter()
        .position(|binding| {
            binding.as_ref().is_some_and(|binding| binding.public_obligation_id == receipt_id)
        })
        .expect("direct receipt maps to one compiler row");
    let target_obligation = dispatched
        .iter()
        .find(|obligation| obligation.obligation_id == receipt_id)
        .expect("receipt obligation remains dispatched");
    assert_eq!(target_obligation.kind, trust_verifier_api::ObligationKind::Ownership);
    assert!(results[target_row].1.is_proved());

    // A byte-identical public run is attribution only when its affine receipt
    // has been discarded. It must fail the strict native authority audit and
    // lose both the proved transport outcome and proof evidence.
    let public_only = vec![None; results.len()];
    assert!(
        native_proved_authority_validation_failures(
            Some(&final_run),
            &results,
            &bindings,
            &public_only,
        )
        .iter()
        .any(|failure| failure.contains(&receipt_id)),
    );
    let public_transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        Some(&final_run),
        &[],
        &bindings,
        &public_only,
    );
    assert_ne!(public_transport[target_row].outcome, Outcome::Proved);
    assert!(public_transport[target_row].proof_evidence.is_none());

    let mut authorities = public_only;
    let report = install_direct_trust_vc_live_authorities(
        &bundle,
        &dispatched,
        &context,
        &final_run,
        Some(&mut live_receipts),
        &results,
        &bindings,
        &mut authorities,
    );
    assert_eq!(report.minted, 1, "{:#?}", report.rejected);
    assert!(report.rejected.is_empty(), "{:#?}", report.rejected);
    let authority = authorities[target_row].as_ref().expect("direct live authority");
    assert!(matches!(authority, ResultProofAuthority::DirectTrustVcLive { .. }));
    assert_eq!(
        trust_disposition_for_authority(
            Some(authority),
            target_row,
            &results[target_row].0,
            &results[target_row].1,
            bindings[target_row].as_ref(),
        ),
        Some((TrustStatus::Trusted, TrustProofStrength::Ownership)),
    );
    assert!(authority.is_static_proof_for(
        target_row,
        &results[target_row].0,
        &results[target_row].1,
        bindings[target_row].as_ref(),
    ));
    assert!(
        apply_vacuity_gate_with_authority(
            target_row,
            &results[target_row].0,
            results[target_row].1.clone(),
            bindings[target_row].as_ref(),
            Some(authority),
        )
        .is_proved(),
        "the exact live receipt, not a public false-shaped label, carries authority",
    );
    assert!(
        !result_row_has_e4_e5_proof_authority(
            target_row,
            &results[target_row].0,
            &results[target_row].1,
            &bindings,
            &authorities,
        ),
        "DirectTrustVcLive must never seed E4/E5 feedback",
    );
    assert!(
        !authority.is_exact_source_clause_body_proof_for(
            target_row,
            &results[target_row].0,
            &results[target_row].1,
            bindings[target_row].as_ref(),
        ),
        "DirectTrustVcLive must never discharge a source-clause body",
    );
    let transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        Some(&final_run),
        &[],
        &bindings,
        &authorities,
    );
    assert_eq!(transport[target_row].outcome, Outcome::Proved);
    let native = transport[target_row]
        .native_trust_ir
        .as_ref()
        .expect("the direct carrier must retain its explicit deferred-native diagnostics");
    assert_eq!(native.suite, "trust-full-verifier");
    assert!(!native.present);
    assert!(native.request_id.is_none());
    assert!(native.native_id.is_none());
    assert!(native.artifacts.is_empty());
    assert!(native.diagnostics.iter().any(|diagnostic| {
        diagnostic.message == trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON
    }));
    let proof_evidence =
        transport[target_row].proof_evidence.as_ref().expect("exact direct proof evidence");
    let expected_transport_strength = trust_types::ProofStrength {
        reasoning: trust_types::ReasoningKind::OwnershipAnalysis,
        assurance: trust_types::AssuranceLevel::Sound,
    };
    assert_eq!(proof_evidence.strength.as_ref(), Some(&expected_transport_strength));
    assert_eq!(
        proof_evidence.evidence.as_ref(),
        Some(&trust_types::ProofEvidence::new(
            trust_types::ReasoningKind::OwnershipAnalysis,
            trust_types::AssuranceLevel::Sound,
        )),
    );
    assert!(
        !proof_evidence.evidence.as_ref().expect("normalized direct evidence").is_certified(),
        "certified public TrustVC evidence maps to sound/Trusted compiler transport, not kernel-certified authority",
    );

    let assert_result_mutation_rejected =
        |candidate_results: &[(VerificationCondition, VerificationResult)], label: &str| {
            assert_eq!(
                trust_disposition_for_authority(
                    authorities[target_row].as_ref(),
                    target_row,
                    &candidate_results[target_row].0,
                    &candidate_results[target_row].1,
                    bindings[target_row].as_ref(),
                ),
                None,
                "{label} must revoke Trusted/Ownership",
            );
            assert!(
                native_proved_authority_validation_failures(
                    Some(&final_run),
                    candidate_results,
                    &bindings,
                    &authorities,
                )
                .iter()
                .any(|failure| failure.contains(&receipt_id)),
                "{label} must fail the final native authority audit",
            );
            let candidate_transport = build_transport_results_with_runtime_checks_bound(
                false,
                None,
                candidate_results,
                Some(&final_run),
                &[],
                &bindings,
                &authorities,
            );
            assert_ne!(candidate_transport[target_row].outcome, Outcome::Proved, "{label}");
            assert!(candidate_transport[target_row].proof_evidence.is_none(), "{label}");
        };

    let mut changed_formula = results.clone();
    changed_formula[target_row].0.formula = Formula::Bool(true);
    assert_result_mutation_rejected(&changed_formula, "formula mutation");

    let mut changed_strength = results.clone();
    let VerificationResult::Proved { strength, .. } = &mut changed_strength[target_row].1 else {
        unreachable!()
    };
    *strength = trust_types::ProofStrength::deductive();
    assert_result_mutation_rejected(&changed_strength, "proof-strength mutation");

    let mut changed_solver = results.clone();
    let VerificationResult::Proved { solver, .. } = &mut changed_solver[target_row].1 else {
        unreachable!()
    };
    *solver = trust_types::Symbol::intern("mutated-after-direct-mint");
    assert_result_mutation_rejected(&changed_solver, "solver mutation");

    let mut changed_certificate = results.clone();
    let VerificationResult::Proved { proof_certificate, .. } =
        &mut changed_certificate[target_row].1
    else {
        unreachable!()
    };
    *proof_certificate = Some(vec![0xde, 0xad, 0xbe, 0xef]);
    assert_result_mutation_rejected(&changed_certificate, "certificate mutation");

    let mut changed_time = results.clone();
    let VerificationResult::Proved { time_ms, .. } = &mut changed_time[target_row].1 else {
        unreachable!()
    };
    *time_ms = (*time_ms).saturating_add(1);
    assert_result_mutation_rejected(&changed_time, "time mutation");

    // A separately modified public carrier cannot borrow the private snapshot,
    // even when it remains a structurally accepted Proved run.
    let mut changed_public_run = final_run.clone();
    changed_public_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == receipt_id)
        .expect("direct accepted evidence")
        .diagnostics
        .push("mutated public diagnostic".to_string());
    assert!(changed_public_run.validate_derived_state().is_ok());
    assert!(
        native_proved_authority_validation_failures(
            Some(&changed_public_run),
            &results,
            &bindings,
            &authorities,
        )
        .iter()
        .any(|failure| failure.contains(&receipt_id)),
    );
    let changed_public_transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        Some(&changed_public_run),
        &[],
        &bindings,
        &authorities,
    );
    assert!(changed_public_transport[target_row].proof_evidence.is_none());

    let rejects_target = |candidate: &[Option<ResultProofAuthority>]| {
        native_proved_authority_validation_failures(
            Some(&final_run),
            &results,
            &bindings,
            candidate,
        )
        .iter()
        .any(|failure| failure.contains(&receipt_id))
    };
    let mut changed_binding = authorities.clone();
    let Some(ResultProofAuthority::DirectTrustVcLive { authority }) =
        changed_binding[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.binding.public_obligation_id.push_str(":changed");
    assert!(rejects_target(&changed_binding));

    let mut changed_authority_evidence = authorities.clone();
    let Some(ResultProofAuthority::DirectTrustVcLive { authority }) =
        changed_authority_evidence[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.accepted_evidence.diagnostics.push("mutated authority evidence".to_string());
    assert!(
        rejects_target(&changed_authority_evidence),
        "a post-mint mutation of the authority's own evidence row must fail closed"
    );

    let mut changed_sealed_evidence = authorities.clone();
    let Some(ResultProofAuthority::DirectTrustVcLive { authority }) =
        changed_sealed_evidence[target_row].as_mut()
    else {
        unreachable!()
    };
    Arc::make_mut(&mut authority.run_seal)
        .final_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == receipt_id)
        .expect("sealed direct evidence")
        .diagnostics
        .push("mutated sealed diagnostic".to_string());
    assert!(rejects_target(&changed_sealed_evidence));

    let mut changed_context = authorities.clone();
    let Some(ResultProofAuthority::DirectTrustVcLive { authority }) =
        changed_context[target_row].as_mut()
    else {
        unreachable!()
    };
    Arc::make_mut(&mut authority.run_seal).context.run_id.push_str(":changed");
    assert!(rejects_target(&changed_context));

    let mut changed_deadline = authorities;
    let Some(ResultProofAuthority::DirectTrustVcLive { authority }) =
        changed_deadline[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.dispatch_deadline = None;
    assert!(rejects_target(&changed_deadline));
}

#[test]
fn direct_trust_vc_final_install_rejects_mutated_evidence_deadline_and_precedence() {
    let mut evidence_fixture = direct_trust_vc_live_fixture("compiler-direct-mint-evidence");
    assert_eq!(evidence_fixture.live_receipts.direct_trust_vc_receipts().len(), 1);
    let evidence_id = evidence_fixture
        .live_receipts
        .direct_trust_vc_receipts()
        .keys()
        .next()
        .expect("one receipt")
        .clone();
    let mut changed_evidence = evidence_fixture.final_run.clone();
    changed_evidence
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == evidence_id)
        .expect("direct accepted evidence")
        .diagnostics
        .push("changed before compiler install".to_string());
    assert!(changed_evidence.validate_derived_state().is_ok());
    let mut evidence_authorities = vec![None; evidence_fixture.results.len()];
    let evidence_report = install_direct_trust_vc_live_authorities(
        &evidence_fixture.bundle,
        &evidence_fixture.dispatched,
        &evidence_fixture.context,
        &changed_evidence,
        Some(&mut evidence_fixture.live_receipts),
        &evidence_fixture.results,
        &evidence_fixture.bindings,
        &mut evidence_authorities,
    );
    assert_eq!(evidence_report.minted, 0);
    assert_eq!(evidence_report.rejected.len(), 1);
    assert!(evidence_report.rejected[0].contains("transition"));

    let mut deadline_fixture = direct_trust_vc_live_fixture("compiler-direct-mint-deadline");
    assert_eq!(deadline_fixture.live_receipts.direct_trust_vc_receipts().len(), 1);
    let original_deadline = deadline_fixture.context.deadline().expect("fixture deadline");
    let changed_context =
        trust_router::VerifierExecutionContext::new(deadline_fixture.context.run_id.clone())
            .with_deadline(original_deadline + std::time::Duration::from_secs(1));
    assert_eq!(changed_context.snapshot(), deadline_fixture.context.snapshot());
    let mut deadline_authorities = vec![None; deadline_fixture.results.len()];
    let deadline_report = install_direct_trust_vc_live_authorities(
        &deadline_fixture.bundle,
        &deadline_fixture.dispatched,
        &changed_context,
        &deadline_fixture.final_run,
        Some(&mut deadline_fixture.live_receipts),
        &deadline_fixture.results,
        &deadline_fixture.bindings,
        &mut deadline_authorities,
    );
    assert_eq!(deadline_report.minted, 0);
    assert_eq!(deadline_report.rejected.len(), 1);
    assert!(deadline_report.rejected[0].contains("deadline"));

    let mut precedence_fixture = direct_trust_vc_live_fixture("compiler-direct-mint-precedence");
    assert_eq!(precedence_fixture.live_receipts.direct_trust_vc_receipts().len(), 1);
    let precedence_id = precedence_fixture
        .live_receipts
        .direct_trust_vc_receipts()
        .keys()
        .next()
        .expect("one receipt")
        .clone();
    let precedence_row = direct_trust_vc_fixture_row(&precedence_fixture, &precedence_id);
    let mut precedence_authorities = vec![None; precedence_fixture.results.len()];
    precedence_authorities[precedence_row] = Some(ResultProofAuthority::KernelCertified {
        row: exact_result_row_identity(
            precedence_row,
            &precedence_fixture.results[precedence_row].0,
        )
        .expect("exact kernel precedence row"),
        evidence: authority_test_clean_cic(0x6d),
    });
    let precedence_report = install_direct_trust_vc_live_authorities(
        &precedence_fixture.bundle,
        &precedence_fixture.dispatched,
        &precedence_fixture.context,
        &precedence_fixture.final_run,
        Some(&mut precedence_fixture.live_receipts),
        &precedence_fixture.results,
        &precedence_fixture.bindings,
        &mut precedence_authorities,
    );
    assert_eq!(precedence_report.minted, 0);
    assert_eq!(precedence_report.rejected.len(), 1);
    assert!(precedence_report.rejected[0].contains("already carries"));
    assert!(matches!(
        precedence_authorities[precedence_row].as_ref(),
        Some(ResultProofAuthority::KernelCertified { .. })
    ));
}

#[test]
fn direct_trust_vc_receipt_survives_exact_unrelated_bridge_publication() {
    let (function, compiler_contracts, mut vcs) = native_trust_ir_compiler_function();
    let mut sep_vc = unsafe_sep_assertion_vc(&function.def_path);
    // Keep this sibling genuinely non-definitive in the native typed-CHC
    // lane, while leaving it exactly decidable by the AY bridge. The old
    // `ptr_0 == 0` fixture is satisfiable, so trust-mc now correctly publishes
    // a definitive Failed row and the bridge must refuse to overwrite it.
    // Floating-point constraints are outside trust-mc's typed-CHC fragment;
    // reflexivity itself remains a strict-UNSAT AY query.
    let fp = trust_types::Formula::Var(
        "bridge_fp".to_string(),
        trust_types::Sort::Float { eb: 8, sb: 24 },
    );
    sep_vc.formula = trust_types::Formula::Not(Box::new(trust_types::Formula::Eq(
        Box::new(fp.clone()),
        Box::new(fp),
    )));
    assert!(
        trust_router::in_process_ay_backend::revalidate_vc_unsat_strict(&sep_vc.formula, 10_000,)
            .is_some(),
        "the bridge sibling must be independently strict-revalidated by AY",
    );
    vcs.push(sep_vc.clone());
    let (bundle, native_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_bundle = native_bundle
        .expect("mixed direct/bridge native bundle must build")
        .expect("mixed direct/bridge fixture requires native requests");
    let dispatched = full_verification_dispatched_obligations(
        &bundle,
        &ExactDefinitionEntryMarkerSet::default(),
    );
    let context = trust_router::VerifierExecutionContext::new("compiler-direct-bridge-mixed");
    let live = verify_full_bundle_with_body_bound_receipts(
        &bundle,
        &dispatched,
        Some(&native_bundle),
        &[],
        &context,
    );
    let mut live_receipts = live.live_receipts.expect("live receipt package");
    assert!(!live_receipts.direct_trust_vc_receipts().is_empty(), "direct sibling receipt");
    let source_run = live.result;
    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &vcs,
        source_run.context.clone(),
    );
    let (legacy_results, legacy_bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &source_run,
        &vcs,
        &snapshot,
    );

    let sep_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation.metadata.iter().any(|entry| entry.key == "trust.vc.hardened.category")
        })
        .expect("hardened bridge sibling");
    assert!(
        !source_run.evidence.iter().any(|evidence| {
            evidence.obligation_id == sep_obligation.obligation_id
                && matches!(
                    evidence.status,
                    trust_verifier_api::EvidenceStatus::Proved
                        | trust_verifier_api::EvidenceStatus::Failed
                )
        }),
        "the bridge sibling fixture must remain non-definitive before publication",
    );
    let bridge_results = vec![(
        sep_vc.clone(),
        VerificationResult::Proved {
            solver: trust_types::Symbol::intern("ay-in-process"),
            time_ms: 1,
            strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(b"mixed direct bridge strict LRAT".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let bridge_bindings =
        vec![test_binding_for_obligation(0, &bridge_results[0].0, sep_obligation)];
    let bridge_authorities =
        bridge_test_solver_revalidated_authorities(&bridge_results, &bridge_bindings);
    let mut final_run = source_run.clone();
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut final_run,
            Some(&native_bundle),
            &bridge_results,
            &bridge_bindings,
            &bridge_authorities,
        ),
        Ok(true),
        "the unrelated non-definitive sibling must publish its exact bridge proof",
    );
    assert!(is_permitted_bridge_publication_transition(&source_run, &final_run));

    let mut authorities = vec![None; legacy_results.len()];
    let expected = live_receipts.direct_trust_vc_receipts().len();
    let report = install_direct_trust_vc_live_authorities(
        &bundle,
        &dispatched,
        &context,
        &final_run,
        Some(&mut live_receipts),
        &legacy_results,
        &legacy_bindings,
        &mut authorities,
    );
    assert_eq!(report.minted, expected, "{:#?}", report.rejected);
    assert!(report.rejected.is_empty(), "{:#?}", report.rejected);
}

struct FreshExactDirectCompilerFixture {
    bundle: trust_verifier_api::TrustContractBundle,
    dispatched: Vec<trust_verifier_api::TrustObligation>,
    context: trust_router::VerifierExecutionContext,
    source_run: trust_verifier_api::VerificationRunResult,
    final_run: trust_verifier_api::VerificationRunResult,
    live_receipts: trust_router::LiveVerificationReceiptBatch,
    results: Vec<(VerificationCondition, VerificationResult)>,
    bindings: Vec<Option<ResultObligationBinding>>,
}

fn fresh_exact_direct_fixture_for(
    function: &trust_types::VerifiableFunction,
    compiler_contracts: &trust_types::CompilerContractBundle,
    vcs: &[VerificationCondition],
    loop_feedback: &[ProofGatedLoopInvariant],
    run_id: &str,
) -> FreshExactDirectCompilerFixture {
    let (bundle, native_bundle) = build_full_verification_input_for_tests_with_loop_feedback(
        function,
        compiler_contracts,
        vcs,
        loop_feedback,
    );
    let native_bundle = native_bundle
        .expect("fresh exact-direct native bundle must build")
        .expect("fresh exact-direct rows require native TrustIr requests");
    let dispatched = full_verification_dispatched_obligations(
        &bundle,
        &ExactDefinitionEntryMarkerSet::default(),
    );
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    let context = trust_router::VerifierExecutionContext::new(run_id).with_deadline(deadline);
    let LiveFullVerificationDispatch { result: final_run, body_bound_receipts, live_receipts } =
        verify_full_bundle_with_body_bound_receipts(
            &bundle,
            &dispatched,
            Some(&native_bundle),
            &[],
            &context,
        );
    assert!(body_bound_receipts.is_empty());
    let live_receipts = live_receipts.expect("live receipt package");
    assert!(live_receipts.direct_trust_vc_receipts().is_empty());
    let snapshot = exact_fresh_vc_rekey_snapshot(
        function,
        compiler_contracts,
        &bundle,
        vcs,
        final_run.context.clone(),
    );
    let (results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        function, &bundle, &final_run, vcs, &snapshot,
    );
    let source_run = final_run.clone();
    FreshExactDirectCompilerFixture {
        bundle,
        dispatched,
        context,
        source_run,
        final_run,
        live_receipts,
        results,
        bindings,
    }
}

fn fresh_exact_direct_e4_fixture(run_id: &str) -> FreshExactDirectCompilerFixture {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();
    function.preconditions.clear();
    function.postconditions.clear();
    let compiler_contracts = trust_types::CompilerContractBundle::new(Vec::new());
    let vcs = vec![
        VerificationCondition {
            kind: VcKind::LoopInvariantInitiation {
                invariant: "i <= n".to_string(),
                header_block: 1,
            },
            function: trust_types::Symbol::intern(&function.def_path),
            location: native_trust_ir_test_span(27),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::LoopInvariantConsecution {
                invariant: "i <= n".to_string(),
                header_block: 1,
            },
            function: trust_types::Symbol::intern(&function.def_path),
            location: native_trust_ir_test_span(28),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
    ];
    fresh_exact_direct_fixture_for(&function, &compiler_contracts, &vcs, &[], run_id)
}

fn fresh_exact_direct_same_span_e4_fixture(run_id: &str) -> FreshExactDirectCompilerFixture {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();
    function.preconditions.clear();
    function.postconditions.clear();
    let compiler_contracts = trust_types::CompilerContractBundle::new(Vec::new());
    let shared_span = native_trust_ir_test_span(29);
    let vcs = vec![
        VerificationCondition {
            kind: VcKind::LoopInvariantInitiation {
                invariant: "i <= n".to_string(),
                header_block: 1,
            },
            function: trust_types::Symbol::intern(&function.def_path),
            location: shared_span.clone(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::LoopInvariantConsecution {
                invariant: "i <= n".to_string(),
                header_block: 1,
            },
            function: trust_types::Symbol::intern(&function.def_path),
            location: shared_span,
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
    ];
    fresh_exact_direct_fixture_for(&function, &compiler_contracts, &vcs, &[], run_id)
}

fn fresh_exact_direct_fixture_row(
    fixture: &FreshExactDirectCompilerFixture,
    public_obligation_id: &str,
) -> usize {
    fixture
        .bindings
        .iter()
        .position(|binding| {
            binding
                .as_ref()
                .is_some_and(|binding| binding.public_obligation_id == public_obligation_id)
        })
        .expect("fresh receipt must retain one exact compiler row binding")
}

#[test]
fn fresh_exact_direct_receipt_mints_s3_and_s4_rejects_public_only_or_mutated_tokens() {
    let FreshExactDirectCompilerFixture {
        bundle,
        dispatched,
        context,
        source_run: _,
        final_run,
        mut live_receipts,
        results,
        bindings,
    } = fresh_exact_direct_e4_fixture("compiler-s3-genuine-route");
    assert_eq!(
        live_receipts.fresh_exact_direct_chc_pdr_receipts().len(),
        2,
        "both exact compiler E4 rows must retain their same-solve affine receipts: {final_run:#?}"
    );
    let receipt_ids = live_receipts
        .fresh_exact_direct_chc_pdr_receipts()
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|(_, result)| result.is_proved()));

    // An identical canonical public Proved run remains attribution-only when
    // its affine sidecars are absent. S4 rejects both rows and transport erases
    // their otherwise plausible public proof envelopes.
    let public_only = vec![None; results.len()];
    let public_failures = native_proved_authority_validation_failures(
        Some(&final_run),
        &results,
        &bindings,
        &public_only,
    );
    assert_eq!(public_failures.len(), receipt_ids.len());
    let public_transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        Some(&final_run),
        &[],
        &bindings,
        &public_only,
    );
    for (row, binding) in bindings.iter().enumerate() {
        if binding
            .as_ref()
            .is_some_and(|binding| receipt_ids.contains(&binding.public_obligation_id))
        {
            assert_ne!(public_transport[row].outcome, Outcome::Proved);
            assert!(public_transport[row].proof_evidence.is_none());
        }
    }

    let mut authorities = public_only;
    let report = install_fresh_exact_direct_chc_pdr_authorities(
        &bundle,
        &dispatched,
        &context,
        &final_run,
        Some(&mut live_receipts),
        &results,
        &bindings,
        &mut authorities,
    );
    assert_eq!(report.minted, receipt_ids.len(), "{:#?}", report.rejected);
    assert!(report.rejected.is_empty(), "{:#?}", report.rejected);
    assert!(authorities.iter().all(|authority| matches!(
        authority,
        Some(ResultProofAuthority::FreshExactDirectChcPdr { .. })
    )));
    for (row, authority) in authorities.iter().enumerate() {
        let authority = authority.as_ref().expect("S3 authority");
        assert!(authority.is_exact_source_clause_body_proof_for(
            row,
            &results[row].0,
            &results[row].1,
            bindings[row].as_ref(),
        ));
        assert_eq!(
            trust_disposition_for_authority(
                Some(authority),
                row,
                &results[row].0,
                &results[row].1,
                bindings[row].as_ref(),
            ),
            Some((TrustStatus::Trusted, TrustProofStrength::Inductive)),
        );
    }
    assert!(
        native_proved_authority_validation_failures(
            Some(&final_run),
            &results,
            &bindings,
            &authorities,
        )
        .is_empty(),
        "genuine receipt-authorized native rows must remain S4-claimable"
    );

    let transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        Some(&final_run),
        &[],
        &bindings,
        &authorities,
    );
    let final_index = build_full_verification_evidence_index(&final_run);
    for (row, authority) in authorities.iter().enumerate() {
        let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) = authority else {
            unreachable!("fixture rows must all carry S3 authority")
        };
        assert_eq!(transport[row].outcome, Outcome::Proved);
        let evidence = final_index
            .evidence_by_evidence_id
            .get(authority.evidence_id.as_str())
            .copied()
            .expect("sealed accepted evidence id");
        let expected_artifacts = evidence
            .artifacts
            .iter()
            .filter(|artifact| !artifact.uri.starts_with("trust_ir-native://"))
            .map(transport_evidence_artifact)
            .collect::<Vec<_>>();
        assert!(!expected_artifacts.is_empty());
        assert_eq!(
            transport[row]
                .proof_evidence
                .as_ref()
                .expect("S3 transport retains exact accepted proof evidence")
                .artifacts,
            expected_artifacts,
        );
    }

    let target_row = 0;
    let target_id =
        bindings[target_row].as_ref().expect("target binding").public_obligation_id.clone();
    let assert_result_mutation_rejected =
        |candidate_results: &[(VerificationCondition, VerificationResult)], label: &str| {
            assert!(
                native_proved_authority_validation_failures(
                    Some(&final_run),
                    candidate_results,
                    &bindings,
                    &authorities,
                )
                .iter()
                .any(|failure| failure.contains(&target_id)),
                "{label} must invalidate S4 native-Proved authority",
            );
            assert_eq!(
                trust_disposition_for_authority(
                    authorities[target_row].as_ref(),
                    target_row,
                    &candidate_results[target_row].0,
                    &candidate_results[target_row].1,
                    bindings[target_row].as_ref(),
                ),
                None,
                "{label} must not retain Trusted/Inductive disposition",
            );
            assert!(
                !result_row_has_e4_e5_proof_authority(
                    target_row,
                    &candidate_results[target_row].0,
                    &candidate_results[target_row].1,
                    &bindings,
                    &authorities,
                ),
                "{label} must not seed E4/E5 feedback",
            );
            assert!(
                !authorities[target_row]
                    .as_ref()
                    .expect("target S3 authority")
                    .is_exact_source_clause_body_proof_for(
                        target_row,
                        &candidate_results[target_row].0,
                        &candidate_results[target_row].1,
                        bindings[target_row].as_ref(),
                    ),
                "{label} must not seed source-clause discharge",
            );
            let candidate_transport = build_transport_results_with_runtime_checks_bound(
                false,
                None,
                candidate_results,
                Some(&final_run),
                &[],
                &bindings,
                &authorities,
            );
            assert_ne!(
                candidate_transport[target_row].outcome, Outcome::Proved,
                "{label} must not transport as proved",
            );
            assert!(
                candidate_transport[target_row].proof_evidence.is_none(),
                "{label} must not retain the sealed public evidence envelope",
            );
        };
    let rejects_target = |candidate: &[Option<ResultProofAuthority>]| {
        native_proved_authority_validation_failures(
            Some(&final_run),
            &results,
            &bindings,
            candidate,
        )
        .iter()
        .any(|failure| failure.contains(&target_id))
    };

    let mut changed_formula_results = results.clone();
    changed_formula_results[target_row].0.formula = Formula::Bool(true);
    assert!(
        native_proved_authority_validation_failures(
            Some(&final_run),
            &changed_formula_results,
            &bindings,
            &authorities,
        )
        .iter()
        .any(|failure| failure.contains(&target_id)),
        "changing the current row formula must invalidate the sealed exact-row capability"
    );

    let mut changed_result_strength = results.clone();
    let VerificationResult::Proved { strength, .. } = &mut changed_result_strength[target_row].1
    else {
        unreachable!()
    };
    *strength = trust_types::ProofStrength::deductive();
    assert_result_mutation_rejected(&changed_result_strength, "compiler proof-strength rewrite");

    let mut changed_result_solver = results.clone();
    let VerificationResult::Proved { solver, .. } = &mut changed_result_solver[target_row].1 else {
        unreachable!()
    };
    *solver = trust_types::Symbol::intern("forged-after-s3-mint");
    assert_result_mutation_rejected(&changed_result_solver, "compiler solver rewrite");

    let mut changed_result_certificate = results.clone();
    let VerificationResult::Proved { proof_certificate, .. } =
        &mut changed_result_certificate[target_row].1
    else {
        unreachable!()
    };
    *proof_certificate = Some(vec![0xde, 0xad, 0xbe, 0xef]);
    assert_result_mutation_rejected(
        &changed_result_certificate,
        "compiler proof-certificate rewrite",
    );

    let mut changed_binding = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_binding[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.binding.public_obligation_id.push_str(":changed");
    assert!(rejects_target(&changed_binding));

    let mut changed_authority_evidence = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_authority_evidence[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.accepted_evidence.diagnostics.push("mutated authority evidence".to_string());
    assert!(rejects_target(&changed_authority_evidence));

    let mut changed_authority_evidence_id = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_authority_evidence_id[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.evidence_id.push_str(":changed");
    assert!(rejects_target(&changed_authority_evidence_id));

    let mut changed_authority_strength = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_authority_strength[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.proof_strength.reasoning =
        if matches!(&authority.proof_strength.reasoning, trust_verifier_api::ReasoningKind::Chc) {
            trust_verifier_api::ReasoningKind::Pdr
        } else {
            trust_verifier_api::ReasoningKind::Chc
        };
    assert!(rejects_target(&changed_authority_strength));

    let mut changed_evidence = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_evidence[target_row].as_mut()
    else {
        unreachable!()
    };
    Arc::make_mut(&mut authority.run_seal)
        .final_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == target_id)
        .expect("sealed evidence row")
        .evidence_id
        .push_str(":changed");
    assert!(rejects_target(&changed_evidence));

    let mut changed_evidence_strength = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_evidence_strength[target_row].as_mut()
    else {
        unreachable!()
    };
    Arc::make_mut(&mut authority.run_seal)
        .final_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == target_id)
        .expect("sealed evidence row")
        .proof_strength = Some(trust_verifier_api::ProofStrength::deductive());
    assert!(rejects_target(&changed_evidence_strength));

    // S4 is bound to the complete evidence row frozen at S3, not merely its
    // public identity and proof strength. Both mutations remain structurally
    // valid public runs, but neither may be paired with the original private
    // authority.
    let mut changed_artifact_run = final_run.clone();
    changed_artifact_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == target_id)
        .expect("sealed evidence row")
        .artifacts
        .iter_mut()
        .find(|artifact| !artifact.uri.starts_with("trust_ir-native://"))
        .expect("accepted proof carries a non-lineage proof artifact")
        .uri
        .push_str(":changed");
    assert!(changed_artifact_run.validate_derived_state().is_ok());
    assert!(
        build_full_verification_evidence_index(&changed_artifact_run)
            .strict_accepted_by_obligation_id
            .contains_key(target_id.as_str()),
        "the artifact substitution must remain an otherwise accepted public proof"
    );
    assert!(
        native_proved_authority_validation_failures(
            Some(&changed_artifact_run),
            &results,
            &bindings,
            &authorities,
        )
        .iter()
        .any(|failure| failure.contains(&target_id)),
        "changing an accepted artifact must invalidate the exact S4 authority"
    );

    let mut changed_diagnostic_run = final_run.clone();
    changed_diagnostic_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == target_id)
        .expect("sealed evidence row")
        .diagnostics
        .push("mutated after compiler mint".to_string());
    assert!(changed_diagnostic_run.validate_derived_state().is_ok());
    assert!(
        build_full_verification_evidence_index(&changed_diagnostic_run)
            .strict_accepted_by_obligation_id
            .contains_key(target_id.as_str()),
        "the diagnostic substitution must remain an otherwise accepted public proof"
    );
    assert!(
        native_proved_authority_validation_failures(
            Some(&changed_diagnostic_run),
            &results,
            &bindings,
            &authorities,
        )
        .iter()
        .any(|failure| failure.contains(&target_id)),
        "changing accepted diagnostics must invalidate the exact S4 authority"
    );

    let mut changed_context = authorities.clone();
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_context[target_row].as_mut()
    else {
        unreachable!()
    };
    Arc::make_mut(&mut authority.run_seal).context.run_id.push_str(":changed");
    assert!(rejects_target(&changed_context));

    let mut changed_deadline = authorities;
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
        changed_deadline[target_row].as_mut()
    else {
        unreachable!()
    };
    authority.dispatch_deadline = None;
    assert!(rejects_target(&changed_deadline));
}

#[test]
fn same_span_fresh_exact_direct_authority_and_transport_are_row_bijective() {
    let FreshExactDirectCompilerFixture {
        bundle,
        dispatched,
        context,
        source_run: _,
        final_run,
        mut live_receipts,
        results,
        bindings,
    } = fresh_exact_direct_same_span_e4_fixture("compiler-s3-same-span-bijection");
    assert_eq!(results.len(), 2);
    let row_a = results
        .iter()
        .position(|(vc, _)| matches!(&vc.kind, VcKind::LoopInvariantInitiation { .. }))
        .expect("same-span fixture has an E4 initiation row");
    let row_b = results
        .iter()
        .position(|(vc, _)| matches!(&vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .expect("same-span fixture has an E4 consecution row");
    assert_ne!(row_a, row_b);
    assert_eq!(results[row_a].0.location, results[row_b].0.location);
    assert_ne!(
        exact_vc_key(&results[row_a].0),
        exact_vc_key(&results[row_b].0),
        "one source span must still contain two distinct exact E4 identities",
    );

    let obligation_id_a = bindings[row_a]
        .as_ref()
        .expect("initiation row has an exact public binding")
        .public_obligation_id
        .clone();
    let obligation_id_b = bindings[row_b]
        .as_ref()
        .expect("consecution row has an exact public binding")
        .public_obligation_id
        .clone();
    assert_ne!(obligation_id_a, obligation_id_b);
    assert_eq!(live_receipts.fresh_exact_direct_chc_pdr_receipts().len(), 2);
    let mut receipt_a = live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&obligation_id_a)
        .expect("split the genuine initiation receipt with its dispatch seal");
    assert!(
        live_receipts.fresh_exact_direct_chc_pdr_receipts().contains_key(&obligation_id_b),
        "leaving B's affine receipt unconsumed is what keeps B fail-closed",
    );

    let mut authorities = vec![None; results.len()];
    let report = install_fresh_exact_direct_chc_pdr_authorities(
        &bundle,
        &dispatched,
        &context,
        &final_run,
        Some(&mut receipt_a),
        &results,
        &bindings,
        &mut authorities,
    );
    assert_eq!(report.minted, 1, "{:#?}", report.rejected);
    assert!(report.rejected.is_empty(), "{:#?}", report.rejected);
    let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority: authority_a }) =
        authorities[row_a].as_ref()
    else {
        panic!("A must carry its genuine same-solve FreshExact authority")
    };
    assert!(authorities[row_b].is_none(), "B must not borrow A's live receipt");
    let final_index = build_full_verification_evidence_index(&final_run);
    let accepted_a = final_index
        .strict_accepted_by_obligation_id
        .get(obligation_id_a.as_str())
        .copied()
        .expect("A has one exact accepted evidence decision");
    assert_eq!(accepted_a, &authority_a.accepted_evidence);
    assert!(authority_a.authorizes_row(row_a, &results[row_a].0, bindings[row_a].as_ref()));
    assert!(authority_a.authorizes_compiler_result(&results[row_a].1));

    let transport = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&final_run),
        &vec![None; results.len()],
        &bindings,
        &authorities,
    );
    assert_eq!(transport[row_a].obligation_id.as_deref(), Some(obligation_id_a.as_str()));
    assert_eq!(transport[row_a].outcome, Outcome::Proved);
    assert!(
        transport[row_a].native_trust_ir.as_ref().is_some_and(|native| native.present),
        "A's native identity and artifacts must come from its accepted evidence row",
    );
    let expected_a_artifacts = accepted_a
        .artifacts
        .iter()
        .filter(|artifact| !artifact.uri.starts_with("trust_ir-native://"))
        .map(transport_evidence_artifact)
        .collect::<Vec<_>>();
    assert!(!expected_a_artifacts.is_empty());
    assert_eq!(
        transport[row_a]
            .proof_evidence
            .as_ref()
            .expect("A transports its exact accepted proof evidence")
            .artifacts,
        expected_a_artifacts,
    );
    assert_eq!(transport[row_b].obligation_id.as_deref(), Some(obligation_id_b.as_str()));
    assert_eq!(
        transport[row_b].outcome, Outcome::Unknown,
        "an E4 loop-contract row has no runtime monitor and must fail closed without authority",
    );
    assert!(transport[row_b].proof_evidence.is_none());

    // Give the adversary the strongest public carrier after swapping A and B:
    // each moved result gets a freshly valid binding at its new position, while
    // the compiler-private authority vector deliberately remains untouched.
    // A's token is still at row_a (which now contains B); A itself moved to
    // row_b (which has no token). Neither row may retain a proved outcome or
    // proof evidence merely because the two exact VCs share one source span.
    let mut reordered_results = results.clone();
    reordered_results.swap(row_a, row_b);
    let obligation_a = dispatched
        .iter()
        .find(|obligation| obligation.obligation_id == obligation_id_a)
        .expect("dispatched A obligation");
    let obligation_b = dispatched
        .iter()
        .find(|obligation| obligation.obligation_id == obligation_id_b)
        .expect("dispatched B obligation");
    let mut reordered_bindings = bindings.clone();
    reordered_bindings[row_a] =
        test_binding_for_obligation(row_a, &reordered_results[row_a].0, obligation_b);
    reordered_bindings[row_b] =
        test_binding_for_obligation(row_b, &reordered_results[row_b].0, obligation_a);
    assert!(
        reordered_bindings[row_a]
            .as_ref()
            .is_some_and(|binding| binding.matches_row(row_a, &reordered_results[row_a].0))
    );
    assert!(
        reordered_bindings[row_b]
            .as_ref()
            .is_some_and(|binding| binding.matches_row(row_b, &reordered_results[row_b].0))
    );

    let reordered = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &reordered_results,
        Some(&final_run),
        &vec![None; results.len()],
        &reordered_bindings,
        &authorities,
    );
    assert_eq!(reordered[row_a].obligation_id.as_deref(), Some(obligation_id_b.as_str()));
    assert_eq!(reordered[row_b].obligation_id.as_deref(), Some(obligation_id_a.as_str()));
    for row in [row_a, row_b] {
        assert_ne!(reordered[row].outcome, Outcome::Proved);
        assert!(
            reordered[row].proof_evidence.is_none(),
            "same-span row {row} borrowed accepted proof evidence after reordering",
        );
    }
    let failures = native_proved_authority_validation_failures(
        Some(&final_run),
        &reordered_results,
        &reordered_bindings,
        &authorities,
    );
    assert!(failures.iter().any(|failure| failure.contains(&obligation_id_a)));
    assert!(failures.iter().any(|failure| failure.contains(&obligation_id_b)));
}

#[test]
fn fresh_exact_direct_receipt_rejects_cross_dispatch_seal_transplant() {
    let mut first = fresh_exact_direct_e4_fixture("compiler-s3-cross-dispatch");
    let second = fresh_exact_direct_e4_fixture("compiler-s3-cross-dispatch");
    let (obligation_id, receipt) = first
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipts()
        .into_iter()
        .next()
        .expect("fresh receipt");
    let obligation = first
        .dispatched
        .iter()
        .find(|obligation| obligation.obligation_id == obligation_id)
        .expect("receipt obligation");
    let evidence = first
        .source_run
        .evidence
        .iter()
        .find(|evidence| evidence.obligation_id == obligation_id)
        .expect("receipt source evidence");
    assert!(
        first
            .live_receipts
            .authorizes_fresh_exact_direct_chc_pdr_receipt(&receipt, obligation, evidence,)
            .is_ok()
    );
    assert!(
        second
            .live_receipts
            .authorizes_fresh_exact_direct_chc_pdr_receipt(&receipt, obligation, evidence,)
            .is_err(),
        "a second live call with the same public run id must have a distinct private seal",
    );
}

#[test]
fn fresh_exact_direct_mint_rejects_mutated_carriers_and_preserves_kernel_precedence() {
    let mut row_and_deadline = fresh_exact_direct_e4_fixture("compiler-s3-mint-row-deadline");
    assert_eq!(row_and_deadline.live_receipts.fresh_exact_direct_chc_pdr_receipts().len(), 2);
    let mut receipt_ids =
        row_and_deadline.live_receipts.fresh_exact_direct_chc_pdr_receipts().keys().cloned();
    let formula_id = receipt_ids.next().expect("first affine E4 receipt");
    let deadline_id = receipt_ids.next().expect("second affine E4 receipt");
    assert!(receipt_ids.next().is_none());
    drop(receipt_ids);
    let mut formula_live_receipts = row_and_deadline
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&formula_id)
        .expect("formula receipt batch");
    let mut deadline_live_receipts = row_and_deadline
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&deadline_id)
        .expect("deadline receipt batch");

    let formula_row = fresh_exact_direct_fixture_row(&row_and_deadline, &formula_id);
    let mut changed_results = row_and_deadline.results.clone();
    changed_results[formula_row].0.formula = Formula::Bool(true);
    let mut formula_authorities = vec![None; changed_results.len()];
    let formula_report = install_fresh_exact_direct_chc_pdr_authorities(
        &row_and_deadline.bundle,
        &row_and_deadline.dispatched,
        &row_and_deadline.context,
        &row_and_deadline.final_run,
        Some(&mut formula_live_receipts),
        &changed_results,
        &row_and_deadline.bindings,
        &mut formula_authorities,
    );
    assert_eq!(formula_report.minted, 0);
    assert_eq!(formula_report.rejected.len(), 1);
    assert!(formula_report.rejected[0].contains(&formula_id));
    assert!(formula_authorities.iter().all(Option::is_none));

    let original_deadline = row_and_deadline.context.deadline().expect("fixture deadline");
    let changed_deadline_context =
        trust_router::VerifierExecutionContext::new(row_and_deadline.context.run_id.clone())
            .with_deadline(original_deadline + std::time::Duration::from_secs(1));
    assert_eq!(
        changed_deadline_context.snapshot(),
        row_and_deadline.context.snapshot(),
        "absolute deadlines are intentionally runtime-private"
    );
    let mut deadline_authorities = vec![None; row_and_deadline.results.len()];
    let deadline_report = install_fresh_exact_direct_chc_pdr_authorities(
        &row_and_deadline.bundle,
        &row_and_deadline.dispatched,
        &changed_deadline_context,
        &row_and_deadline.final_run,
        Some(&mut deadline_live_receipts),
        &row_and_deadline.results,
        &row_and_deadline.bindings,
        &mut deadline_authorities,
    );
    assert_eq!(deadline_report.minted, 0);
    assert_eq!(deadline_report.rejected.len(), 1);
    assert!(deadline_report.rejected[0].contains(&deadline_id));
    assert!(deadline_report.rejected[0].contains("deadline"));

    let mut evidence_mutations = fresh_exact_direct_e4_fixture("compiler-s3-mint-evidence");
    assert_eq!(evidence_mutations.live_receipts.fresh_exact_direct_chc_pdr_receipts().len(), 2);
    let mut receipt_ids =
        evidence_mutations.live_receipts.fresh_exact_direct_chc_pdr_receipts().keys().cloned();
    let identity_id = receipt_ids.next().expect("identity receipt");
    let strength_id = receipt_ids.next().expect("strength receipt");
    assert!(receipt_ids.next().is_none());
    drop(receipt_ids);
    let mut identity_live_receipts = evidence_mutations
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&identity_id)
        .expect("identity receipt batch");
    let mut strength_live_receipts = evidence_mutations
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&strength_id)
        .expect("strength receipt batch");

    let mut identity_evidence = evidence_mutations.final_run.evidence.clone();
    identity_evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == identity_id)
        .expect("accepted identity evidence")
        .evidence_id
        .push_str(":changed");
    let identity_run = trust_verifier_api::VerificationRunResult::from_evidence(
        evidence_mutations.final_run.context.clone(),
        &evidence_mutations.bundle,
        evidence_mutations.final_run.engine.clone(),
        &evidence_mutations.dispatched,
        identity_evidence,
    );
    assert!(identity_run.validate_derived_state().is_ok());
    let mut identity_authorities = vec![None; evidence_mutations.results.len()];
    let identity_report = install_fresh_exact_direct_chc_pdr_authorities(
        &evidence_mutations.bundle,
        &evidence_mutations.dispatched,
        &evidence_mutations.context,
        &identity_run,
        Some(&mut identity_live_receipts),
        &evidence_mutations.results,
        &evidence_mutations.bindings,
        &mut identity_authorities,
    );
    assert_eq!(identity_report.minted, 0);
    assert_eq!(identity_report.rejected.len(), 1);
    assert!(identity_report.rejected[0].contains(&identity_id));

    let mut strength_evidence = evidence_mutations.final_run.evidence.clone();
    let changed_strength = strength_evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == strength_id)
        .expect("accepted strength evidence");
    assert_ne!(
        changed_strength.proof_strength.as_ref(),
        Some(&trust_verifier_api::ProofStrength::deductive())
    );
    changed_strength.proof_strength = Some(trust_verifier_api::ProofStrength::deductive());
    let strength_run = trust_verifier_api::VerificationRunResult::from_evidence(
        evidence_mutations.final_run.context.clone(),
        &evidence_mutations.bundle,
        evidence_mutations.final_run.engine.clone(),
        &evidence_mutations.dispatched,
        strength_evidence,
    );
    assert!(strength_run.validate_derived_state().is_ok());
    let mut strength_authorities = vec![None; evidence_mutations.results.len()];
    let strength_report = install_fresh_exact_direct_chc_pdr_authorities(
        &evidence_mutations.bundle,
        &evidence_mutations.dispatched,
        &evidence_mutations.context,
        &strength_run,
        Some(&mut strength_live_receipts),
        &evidence_mutations.results,
        &evidence_mutations.bindings,
        &mut strength_authorities,
    );
    assert_eq!(strength_report.minted, 0);
    assert_eq!(strength_report.rejected.len(), 1);
    assert!(strength_report.rejected[0].contains(&strength_id));

    let mut composite_mutations =
        fresh_exact_direct_e4_fixture("compiler-s3-mint-composite-evidence");
    assert_eq!(composite_mutations.live_receipts.fresh_exact_direct_chc_pdr_receipts().len(), 2);
    let mut receipt_ids =
        composite_mutations.live_receipts.fresh_exact_direct_chc_pdr_receipts().keys().cloned();
    let artifact_id = receipt_ids.next().expect("artifact receipt");
    let diagnostic_id = receipt_ids.next().expect("diagnostic receipt");
    assert!(receipt_ids.next().is_none());
    drop(receipt_ids);
    let mut artifact_live_receipts = composite_mutations
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&artifact_id)
        .expect("artifact receipt batch");
    let mut diagnostic_live_receipts = composite_mutations
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&diagnostic_id)
        .expect("diagnostic receipt batch");

    let mut artifact_evidence = composite_mutations.final_run.evidence.clone();
    artifact_evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == artifact_id)
        .expect("accepted artifact evidence")
        .artifacts
        .iter_mut()
        .find(|artifact| !artifact.uri.starts_with("trust_ir-native://"))
        .expect("accepted proof carries a non-lineage proof artifact")
        .uri
        .push_str(":changed");
    let artifact_run = trust_verifier_api::VerificationRunResult::from_evidence(
        composite_mutations.final_run.context.clone(),
        &composite_mutations.bundle,
        composite_mutations.final_run.engine.clone(),
        &composite_mutations.dispatched,
        artifact_evidence,
    );
    assert!(artifact_run.validate_derived_state().is_ok());
    let mut artifact_authorities = vec![None; composite_mutations.results.len()];
    let artifact_report = install_fresh_exact_direct_chc_pdr_authorities(
        &composite_mutations.bundle,
        &composite_mutations.dispatched,
        &composite_mutations.context,
        &artifact_run,
        Some(&mut artifact_live_receipts),
        &composite_mutations.results,
        &composite_mutations.bindings,
        &mut artifact_authorities,
    );
    assert_eq!(artifact_report.minted, 0);
    assert_eq!(artifact_report.rejected.len(), 1);
    assert!(artifact_report.rejected[0].contains(&artifact_id));
    assert!(artifact_report.rejected[0].contains("transition"));

    let mut diagnostic_evidence = composite_mutations.final_run.evidence.clone();
    diagnostic_evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == diagnostic_id)
        .expect("accepted diagnostic evidence")
        .diagnostics
        .push("mutated after native solve".to_string());
    let diagnostic_run = trust_verifier_api::VerificationRunResult::from_evidence(
        composite_mutations.final_run.context.clone(),
        &composite_mutations.bundle,
        composite_mutations.final_run.engine.clone(),
        &composite_mutations.dispatched,
        diagnostic_evidence,
    );
    assert!(diagnostic_run.validate_derived_state().is_ok());
    let mut diagnostic_authorities = vec![None; composite_mutations.results.len()];
    let diagnostic_report = install_fresh_exact_direct_chc_pdr_authorities(
        &composite_mutations.bundle,
        &composite_mutations.dispatched,
        &composite_mutations.context,
        &diagnostic_run,
        Some(&mut diagnostic_live_receipts),
        &composite_mutations.results,
        &composite_mutations.bindings,
        &mut diagnostic_authorities,
    );
    assert_eq!(diagnostic_report.minted, 0);
    assert_eq!(diagnostic_report.rejected.len(), 1);
    assert!(diagnostic_report.rejected[0].contains(&diagnostic_id));
    assert!(diagnostic_report.rejected[0].contains("transition"));

    let mut context_and_kernel = fresh_exact_direct_e4_fixture("compiler-s3-mint-context-kernel");
    assert_eq!(context_and_kernel.live_receipts.fresh_exact_direct_chc_pdr_receipts().len(), 2);
    let mut receipt_ids =
        context_and_kernel.live_receipts.fresh_exact_direct_chc_pdr_receipts().keys().cloned();
    let context_id = receipt_ids.next().expect("context receipt");
    let kernel_id = receipt_ids.next().expect("kernel receipt");
    assert!(receipt_ids.next().is_none());
    drop(receipt_ids);
    let mut context_live_receipts = context_and_kernel
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&context_id)
        .expect("context receipt batch");
    let mut kernel_live_receipts = context_and_kernel
        .live_receipts
        .take_fresh_exact_direct_chc_pdr_receipt_batch(&kernel_id)
        .expect("kernel receipt batch");

    let wrong_context = trust_router::VerifierExecutionContext::new("different-compiler-run")
        .with_deadline(context_and_kernel.context.deadline().expect("fixture deadline"));
    let mut context_authorities = vec![None; context_and_kernel.results.len()];
    let context_report = install_fresh_exact_direct_chc_pdr_authorities(
        &context_and_kernel.bundle,
        &context_and_kernel.dispatched,
        &wrong_context,
        &context_and_kernel.final_run,
        Some(&mut context_live_receipts),
        &context_and_kernel.results,
        &context_and_kernel.bindings,
        &mut context_authorities,
    );
    assert_eq!(context_report.minted, 0);
    assert_eq!(context_report.rejected.len(), 1);
    assert!(context_report.rejected[0].contains(&context_id));
    assert!(context_report.rejected[0].contains("execution context"));

    let kernel_row = fresh_exact_direct_fixture_row(&context_and_kernel, &kernel_id);
    let mut kernel_authorities = vec![None; context_and_kernel.results.len()];
    kernel_authorities[kernel_row] = Some(ResultProofAuthority::KernelCertified {
        row: exact_result_row_identity(kernel_row, &context_and_kernel.results[kernel_row].0)
            .expect("exact kernel precedence row"),
        evidence: authority_test_clean_cic(0x5a),
    });
    let kernel_report = install_fresh_exact_direct_chc_pdr_authorities(
        &context_and_kernel.bundle,
        &context_and_kernel.dispatched,
        &context_and_kernel.context,
        &context_and_kernel.final_run,
        Some(&mut kernel_live_receipts),
        &context_and_kernel.results,
        &context_and_kernel.bindings,
        &mut kernel_authorities,
    );
    assert_eq!(kernel_report.minted, 0);
    assert_eq!(kernel_report.rejected.len(), 1);
    assert!(kernel_report.rejected[0].contains(&kernel_id));
    assert!(kernel_report.rejected[0].contains("already carries"));
    assert!(matches!(
        kernel_authorities[kernel_row].as_ref(),
        Some(ResultProofAuthority::KernelCertified { .. })
    ));
}

/// The motivating suppression bug involved a diverging `panic!` call, not a
/// MIR `Assert`: that call has no direct public VC and is covered only by the
/// bridge's counted whole-function panic-freedom row. Keep that exact shape in
/// the monotonicity gate so adding E4/E5 work can never make it disappear.
#[test]
fn loop_vcs_do_not_suppress_no_return_panic_call_obligation() {
    let (mut function, compiler_contracts, _) = native_trust_ir_compiler_function();
    function.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: Vec::new(),
        terminator: trust_types::Terminator::Call {
            func: "core::panicking::panic".to_string(),
            args: Vec::new(),
            dest: trust_types::Place::local(0),
            target: None,
            span: native_trust_ir_test_span(30),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: trust_types::UnwindEdge::Unreachable,
        },
    }];

    let vc = |kind, line| VerificationCondition {
        kind,
        function: trust_types::Symbol::intern("demo::checked_transfer"),
        location: native_trust_ir_test_span(line),
        formula: trust_types::Formula::Bool(false),
        contract_metadata: None,
    };
    let baseline_vcs = vec![vc(
        VcKind::UnboundedAllocation {
            callee: "Vec::with_capacity".to_string(),
            count: "n".to_string(),
            detail: "no dominating allocation bound".to_string(),
        },
        31,
    )];
    let mut enriched_vcs = baseline_vcs.clone();
    enriched_vcs.extend([
        vc(
            VcKind::LoopInvariantInitiation { invariant: "i <= n".to_string(), header_block: 1 },
            32,
        ),
        vc(
            VcKind::LoopInvariantConsecution { invariant: "i <= n".to_string(), header_block: 1 },
            33,
        ),
        vc(
            VcKind::NonTermination {
                context: "loop-decreases".to_string(),
                measure: "n - i".to_string(),
            },
            34,
        ),
    ]);

    let (baseline, baseline_native) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &baseline_vcs);
    baseline_native
        .expect("baseline native bundle should build")
        .expect("diverging panic call requires a native trust-mc request");
    let (enriched, enriched_native) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &enriched_vcs);
    enriched_native
        .expect("loop-enriched native bundle should build")
        .expect("diverging panic plus E4/E5 rows require native requests");

    fn panic_row(
        bundle: &trust_verifier_api::TrustContractBundle,
    ) -> Option<&trust_verifier_api::TrustObligation> {
        bundle.obligations.iter().find(|obligation| {
            obligation.metadata.iter().any(|entry| {
                entry.key == TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY
                    && entry.value == "enabled"
            })
        })
    }
    let baseline_panic = panic_row(&baseline).expect("baseline must count panic freedom");
    let enriched_panic = panic_row(&enriched).expect("E4/E5 must not suppress panic freedom");
    assert_eq!(
        baseline_panic.obligation_id, enriched_panic.obligation_id,
        "adding E4/E5 obligations must preserve the exact no-return panic row"
    );

    let baseline_ids = baseline
        .obligations
        .iter()
        .map(|obligation| obligation.obligation_id.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    let enriched_ids = enriched
        .obligations
        .iter()
        .map(|obligation| obligation.obligation_id.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        baseline_ids.is_subset(&enriched_ids),
        "adding E4/E5 obligations must preserve every baseline obligation, including allocation"
    );
}
#[test]
fn unsupported_trust_vc_native_import_surfaces_structured_transport_row() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-trust-vc-unsupported-import",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: "obligation:demo::checked_transfer:ownership:unsupported".to_string(),
        kind: trust_verifier_api::ObligationKind::Ownership,
        contract_id: None,
        proof_item_id: None,
        source: native_trust_ir_test_source_location(99),
        description: "ownership requires trust-vc native import".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    });

    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
            .expect("unsupported trust-vc import should not fail native bundle planning");
    assert!(
        native_trust_ir_bundle.is_some(),
        "default trust-mc should still synthesize a valid native TrustIr bundle"
    );
    let obligation = bundle.obligations.first().expect("trust-vc obligation should remain");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
        ),
        "trust-vc"
    );
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY
        ),
        "unsupported"
    );
    let unsupported_reason = test_obligation_metadata(
        obligation,
        super::TRUST_TRUST_IR_NATIVE_UNSUPPORTED_REASON_METADATA_KEY,
    );
    assert!(unsupported_reason.contains("missing `trust_vc.mir_memory.proof_unit`"));

    let mut trust_vc_manifest = trust_verifier_api::EngineManifest::new(
        "trust-vc",
        "native-trust-ir-test",
        trust_verifier_api::EngineKind::Deductive,
    );
    trust_vc_manifest.repository = Some("trust-vc-bridge".to_string());
    let evidence = trust_verifier_api::ObligationEvidence {
        evidence_id: "trust-vc:unsupported:ownership".to_string(),
        obligation_id: obligation.obligation_id.clone(),
        engine: trust_vc_manifest,
        status: trust_verifier_api::EvidenceStatus::Unsupported,
        proof_strength: None,
        artifacts: Vec::new(),
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: vec![unsupported_reason.to_string()],
    };
    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("trust-vc-unsupported-transport-test")
            .snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        vec![evidence],
    );
    let transport_results =
        bound_full_transport_results_for_test(true, &function, &bundle, &full_result);

    let row = transport_results
        .iter()
        .find(|row| row.obligation_id.as_deref() == Some(obligation.obligation_id.as_str()))
        .expect("transport results should include the trust-vc unsupported row");
    assert_eq!(row.obligation_id.as_deref(), Some(obligation.obligation_id.as_str()));
    let native =
        row.native_trust_ir.as_ref().expect("trust-vc unsupported import should have native row");
    assert_eq!(native.suite, "trust-vc");
    assert!(!native.present);
    assert!(native.request_id.is_none());
    assert!(native.native_id.is_none());
    assert!(native.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "native_trust_ir_unsupported"
            && diagnostic.message.contains("missing `trust_vc.mir_memory.proof_unit`")
    }));

    let proof = row
        .proof_evidence
        .as_ref()
        .expect("trust-vc unsupported import should have proof evidence row");
    assert_eq!(proof.suite, "trust-vc");
    assert_eq!(proof.status, trust_types::TransportProofStatus::Unsupported);
}

#[test]
fn rejected_trust_vc_native_import_surfaces_structured_transport_row() {
    let (function, _, _) = native_trust_ir_compiler_function();
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-trust-vc-rejected-import",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: "obligation:demo::checked_transfer:ownership:rejected".to_string(),
        kind: trust_verifier_api::ObligationKind::Ownership,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "ownership carries malformed trust-vc native import".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![trust_verifier_api::MetadataEntry {
            key: super::TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
            value: "{".to_string(),
        }],
    });

    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
            .expect("rejected trust-vc import should not fail native bundle planning");
    assert!(
        native_trust_ir_bundle.is_some(),
        "default trust-mc should still synthesize a valid native TrustIr bundle"
    );
    let obligation = bundle.obligations.first().expect("trust-vc obligation should remain");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
        ),
        "trust-vc"
    );
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY
        ),
        "rejected"
    );
    let rejected_reason = test_obligation_metadata(
        obligation,
        super::TRUST_TRUST_IR_NATIVE_UNSUPPORTED_REASON_METADATA_KEY,
    );
    assert!(rejected_reason.contains("rejected"));

    let mut trust_vc_manifest = trust_verifier_api::EngineManifest::new(
        "trust-vc",
        "native-trust-ir-test",
        trust_verifier_api::EngineKind::Deductive,
    );
    trust_vc_manifest.repository = Some("trust-vc-bridge".to_string());
    let evidence = trust_verifier_api::ObligationEvidence {
        evidence_id: "trust-vc:rejected:ownership".to_string(),
        obligation_id: obligation.obligation_id.clone(),
        engine: trust_vc_manifest,
        status: trust_verifier_api::EvidenceStatus::Unsupported,
        proof_strength: None,
        artifacts: Vec::new(),
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: vec![rejected_reason.to_string()],
    };
    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("trust-vc-rejected-transport-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        vec![evidence],
    );
    let transport_results =
        bound_full_transport_results_for_test(true, &function, &bundle, &full_result);

    let row = transport_results
        .iter()
        .find(|row| row.obligation_id.as_deref() == Some(obligation.obligation_id.as_str()))
        .expect("transport results should include the trust-vc rejected row");
    assert_eq!(row.obligation_id.as_deref(), Some(obligation.obligation_id.as_str()));
    let native =
        row.native_trust_ir.as_ref().expect("trust-vc rejected import should have native row");
    assert_eq!(native.suite, "trust-vc");
    assert!(!native.present);
    assert!(native.request_id.is_none());
    assert!(native.native_id.is_none());
    assert!(native.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "native_trust_ir_transport_status"
            && diagnostic.message.contains("rejected")
    }));
    assert!(native.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "native_trust_ir_rejected" && diagnostic.message.contains("rejected")
    }));

    let proof = row
        .proof_evidence
        .as_ref()
        .expect("trust-vc rejected import should have proof evidence row");
    assert_eq!(proof.suite, "trust-vc");
    assert_eq!(proof.status, trust_types::TransportProofStatus::Unsupported);
}

/// Trust (sealed-authority S2/S3 reconciliation) fixture: a trust-vc-routed
/// BoundsCheck obligation minted by the real compiler-identity
/// `function_to_verifier_api_bundle` path from `all_vcs[0]`. Using the real mint is
/// essential here: planning authority requires the complete function/crate,
/// id, source-span, digest, formula, and TrustVC metadata identity, not a
/// hand-built row that merely copies an origin index and description.
fn kernel_certified_trust_vc_fixture(
    formula: trust_types::Formula,
) -> (
    trust_types::VerifiableFunction,
    trust_verifier_api::TrustContractBundle,
    Vec<VerificationCondition>,
) {
    let (function, compiler_contracts, _) = native_trust_ir_compiler_function();
    let vc = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: trust_types::Symbol::intern(&function.def_path),
        location: native_trust_ir_test_span(12),
        formula,
        contract_metadata: None,
    };
    let bundle = trust_mir_extract::function_to_verifier_api_bundle_with_compiler_identity(
        &function,
        &compiler_contracts,
        std::slice::from_ref(&vc),
        "demo",
        0xd3_0000_0000_0001,
    );
    (function, bundle, vec![vc])
}

/// The `verify_index_oob_safe` bounds-check violation family: type-range facts,
/// the dominating path guard `idx <u 10`, and the violation
/// `violation_bound ≤u idx`. With `violation_bound = 10` the pool is the exact
/// unsigned-order contradiction `certify_unsigned_bv_order_contradiction`
/// kernel-certifies; with `violation_bound = 5` it is satisfiable (`idx = 7`)
/// and the kernel declines.
fn unsigned_bv_order_violation_formula(violation_bound: i128) -> trust_types::Formula {
    let w = 64u32;
    let idx =
        || Box::new(trust_types::Formula::Var("idx".to_string(), trust_types::Sort::BitVec(w)));
    let bv = |value: i128| Box::new(trust_types::Formula::BitVec { value, width: w });
    trust_types::Formula::And(vec![
        trust_types::Formula::And(vec![
            trust_types::Formula::BvULe(bv(0), idx(), w),
            trust_types::Formula::BvULe(idx(), bv(u64::MAX as i128), w),
        ]),
        trust_types::Formula::BvULt(idx(), bv(10), w),
        trust_types::Formula::BvULe(bv(violation_bound), idx(), w),
    ])
}

/// Trust (sealed-authority S2/S3 reconciliation): a trust-vc-routed obligation
/// whose own source VC the clean CIC kernel certifies through the bounded,
/// shape-specific planning recognizer is EXCLUDED from the native module: no
/// trust-vc request is
/// planned and no unreplayable imported certificate can reach — and fail-close
/// — the bundle. This is the `verify_index_oob_safe` tip conflict: the same
/// obligation's transport row is kernel-certified Proved, so the bundle must
/// never depend on the unreplayable trust-vc lane for it.
#[test]
fn kernel_certified_trust_vc_obligation_is_excluded_from_native_trust_vc_lane() {
    let (function, mut bundle, vcs) =
        kernel_certified_trust_vc_fixture(unsigned_bv_order_violation_formula(10));
    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &vcs)
            .expect("kernel-certified trust-vc exclusion must not fail native bundle planning")
            .expect("default trust-mc should still synthesize a native TrustIr bundle");

    assert!(
        !native_trust_ir_bundle.requests.iter().any(|request| matches!(
            request.verifier_suite(),
            trust_ir::NativeVerifierSuite::TrustVc
        )),
        "a kernel-certified obligation must not plan a trust-vc request"
    );
    assert!(
        native_trust_ir_bundle.module.proof_certificates.is_empty(),
        "no unreplayable trust-vc certificate may be attached to the bundle"
    );
    assert!(
        native_trust_ir_bundle
            .module
            .proof_obligations
            .iter()
            .all(|obligation| obligation.kind != trust_ir::ObligationKind::MemorySafety),
        "the excluded obligation must not enter the native module's proof inventory"
    );

    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::BoundsCheck)
        .expect("the bounds obligation should remain in the public bundle");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY
        ),
        "kernel_certified"
    );
    assert_eq!(
        test_obligation_metadata(
            obligation,
            trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
        ),
        "trust-vc"
    );
}

#[test]
fn kernel_excluded_bounds_row_reaches_certified_result_and_transport_authority() {
    let (function, _, vcs) =
        kernel_certified_trust_vc_fixture(unsigned_bv_order_violation_formula(10));
    let vc = vcs.into_iter().next().expect("one guarded-index VC");
    let unknown = || VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-vc-native-excluded"),
        time_ms: 1,
        reason: "no matching native TrustVC request was planned".to_string(),
    };

    let mut results = vec![(vc.clone(), unknown())];
    promote_kernel_certifiable(&mut results, None);
    assert!(matches!(
        &results[0].1,
        VerificationResult::Proved { solver, .. }
            if solver.as_str() == "clean-kernel-certified"
    ));
    let cleancic = certify_all(&results, None);
    assert!(matches!(cleancic.as_slice(), [Some(trust_ir::ProofEvidence::CleanCic { .. })]));
    let bindings = vec![None];
    let authorities = build_result_proof_authorities(&results, &bindings, None, &cleancic);
    assert!(matches!(authorities.as_slice(), [Some(ResultProofAuthority::KernelCertified { .. })]));

    let proof_results = build_proof_results_with_runtime_checks(
        false,
        &results,
        &[],
        &bindings,
        &authorities,
        Some(&function),
    );
    assert_eq!(
        proof_results.dispositions[ObligationId::from_usize(0)].status,
        TrustStatus::Certified
    );
    let transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        None,
        &cleancic,
        &bindings,
        &authorities,
    );
    assert_eq!(transport[0].outcome, Outcome::Proved);
    assert!(transport[0].proof_evidence.is_some());

    let mut expired = vec![(vc, unknown())];
    let past = std::time::Instant::now() - std::time::Duration::from_secs(1);
    promote_kernel_certifiable(&mut expired, Some(past));
    assert!(matches!(expired[0].1, VerificationResult::Unknown { .. }));
    let expired_cleancic = certify_all(&expired, Some(past));
    assert!(expired_cleancic.iter().all(Option::is_none));
}

/// FAIL-CLOSED: a satisfiable guard/violation pair (`idx <u 10` with
/// `5 ≤u idx`) is NOT kernel-certifiable, so the planning-time exclusion must
/// not fire. The exact conservative outcome may be a direct-lane refutation,
/// deferral, or native request; it must never claim planning-time kernel
/// certification.
#[test]
fn kernel_uncertifiable_trust_vc_obligation_keeps_conservative_fail_closed_lane() {
    let (function, mut bundle, vcs) =
        kernel_certified_trust_vc_fixture(unsigned_bv_order_violation_formula(5));
    build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &vcs)
        .expect("an unavailable trust-vc import should not fail native bundle planning")
        .expect("default trust-mc should still synthesize a native TrustIr bundle");

    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::BoundsCheck)
        .expect("the bounds obligation should remain in the public bundle");
    assert_ne!(
        obligation
            .metadata
            .iter()
            .find(|entry| {
                entry.key == super::TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY
            })
            .map(|entry| entry.value.as_str()),
        Some("kernel_certified"),
        "a kernel-declined obligation must keep the conservative lane"
    );
}

/// FAIL-CLOSED (identity binding): the exclusion may consume a kernel
/// certificate only for the obligation's OWN source VC. A row whose
/// `description` does not match the origin-indexed VC (the synthetic
/// panic-freedom catch-all shape, which stamps `vc_index: 0` without a VC row)
/// must not bind — and must keep the conservative lane even though `all_vcs[0]`
/// itself is kernel-certifiable.
#[test]
fn kernel_certified_exclusion_requires_exact_vc_identity_binding() {
    let (function, mut bundle, vcs) =
        kernel_certified_trust_vc_fixture(unsigned_bv_order_violation_formula(10));
    let bounds_index = bundle
        .obligations
        .iter()
        .position(|obligation| obligation.kind == trust_verifier_api::ObligationKind::BoundsCheck)
        .expect("fixture contains a bounds obligation");
    bundle.obligations[bounds_index].description =
        "some other obligation's description".to_string();
    build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &vcs)
        .expect("an unavailable trust-vc import should not fail native bundle planning")
        .expect("default trust-mc should still synthesize a native TrustIr bundle");

    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::BoundsCheck)
        .expect("the bounds obligation should remain in the public bundle");
    assert_ne!(
        obligation
            .metadata
            .iter()
            .find(|entry| {
                entry.key == super::TRUST_TRUST_IR_NATIVE_TRANSPORT_STATUS_METADATA_KEY
            })
            .map(|entry| entry.value.as_str()),
        Some("kernel_certified"),
        "a mismatched VC identity must never consume the kernel certificate"
    );
}

#[test]
fn native_planning_vc_binding_reuses_full_fresh_identity_and_rejects_ambiguity() {
    let (function, bundle, vcs) =
        kernel_certified_trust_vc_fixture(unsigned_bv_order_violation_formula(10));
    let bounds_index = bundle
        .obligations
        .iter()
        .position(|obligation| obligation.kind == trust_verifier_api::ObligationKind::BoundsCheck)
        .expect("fixture contains a bounds obligation");
    let binding = |candidate: &trust_verifier_api::TrustContractBundle,
                   candidate_vcs: &[VerificationCondition]| {
        exact_native_planning_vc_indices(&function, candidate, candidate_vcs)
            .get(bounds_index)
            .copied()
            .flatten()
    };
    assert_eq!(binding(&bundle, &vcs), Some(0));

    let mut wrong_id = bundle.clone();
    wrong_id.obligations[bounds_index].obligation_id.push_str(":forged");
    assert_eq!(binding(&wrong_id, &vcs), None);

    let mut wrong_kind = bundle.clone();
    wrong_kind.obligations[bounds_index].kind = trust_verifier_api::ObligationKind::MemorySafety;
    assert_eq!(binding(&wrong_kind, &vcs), None);

    let mut forged_contract_link = bundle.clone();
    forged_contract_link.obligations[bounds_index].contract_id =
        Some("contract:demo__checked_transfer:0:ensures".to_string());
    assert_eq!(binding(&forged_contract_link, &vcs), None);

    for source_key in [
        super::TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY,
        super::TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
        super::TRUST_VC_SOURCE_CONTRACT_ROLE_METADATA_KEY,
    ] {
        let mut forged_source_link = bundle.clone();
        forged_source_link.obligations[bounds_index].metadata.push(
            trust_verifier_api::MetadataEntry {
                key: source_key.to_string(),
                value: "forged".to_string(),
            },
        );
        assert_eq!(binding(&forged_source_link, &vcs), None, "source key {source_key}");
    }

    let mut wrong_digest = bundle.clone();
    wrong_digest.obligations[bounds_index]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == super::TRUST_VC_DIGEST_METADATA_KEY)
        .expect("fresh VC carries its digest")
        .value = "0".repeat(64);
    assert_eq!(binding(&wrong_digest, &vcs), None);

    let mut wrong_context = bundle.clone();
    let context_entry = wrong_context.obligations[bounds_index]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
        .expect("fresh VC carries typed context");
    let mut context = trust_verifier_api::ObligationContext::from_metadata_entry(context_entry)
        .expect("typed context parses")
        .expect("entry is a typed context");
    context.function.as_mut().expect("fresh context names its function").path.push_str("::forged");
    *context_entry = context.to_metadata_entry().expect("mutated context serializes");
    assert_eq!(binding(&wrong_context, &vcs), None);

    let mut wrong_schema = bundle.clone();
    let context_entry = wrong_schema.obligations[bounds_index]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
        .expect("fresh VC carries typed context");
    let mut context = trust_verifier_api::ObligationContext::from_metadata_entry(context_entry)
        .expect("typed context parses")
        .expect("entry is a typed context");
    if let trust_verifier_api::ObligationOrigin::VerificationCondition { formula_schema, .. } =
        &mut context.origin
    {
        *formula_schema = Some("trust.formula.forged".to_string());
    } else {
        panic!("fixture must have a VC origin");
    }
    *context_entry = context.to_metadata_entry().expect("mutated context serializes");
    assert_eq!(binding(&wrong_schema, &vcs), None);

    let mut duplicate = bundle.clone();
    duplicate.obligations.push(duplicate.obligations[bounds_index].clone());
    assert_eq!(binding(&duplicate, &vcs), None, "two exact rows make the VC ambiguous");

    let mut wrong_subject = bundle.clone();
    let trust_verifier_api::BundleSubject::Function { crate_name, .. } = &mut wrong_subject.subject
    else {
        panic!("fixture is function-scoped");
    };
    *crate_name = "other_crate".to_string();
    assert_eq!(binding(&wrong_subject, &vcs), None);
}

#[test]
fn proof_unit_metadata_alone_does_not_synthesize_trust_vc_certificate() {
    let proof_unit = serde_json::json!({
        "source_id": "src/lib.rs:demo::borrow",
        "unit_id": "metadata-only-unit",
        "obligations": [
            { "id": "obligation:demo::borrow:memory:0" }
        ],
    });
    let mut canonical_proof_unit = String::new();
    write_canonical_json_value(&proof_unit, &mut canonical_proof_unit)
        .expect("direct proof-unit fixture canonicalizes");
    let proof_unit = canonical_proof_unit;
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "obligation:demo::borrow:memory:0".to_string(),
        kind: trust_verifier_api::ObligationKind::MemorySafety,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "memory safety".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![trust_verifier_api::MetadataEntry {
            key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
            value: proof_unit,
        }],
    };

    match trust_vc_native_trust_ir_certificate_import(&obligation) {
        TrustVcNativeTrustIrCertificateImport::Unavailable { .. } => {}
        TrustVcNativeTrustIrCertificateImport::NotApplicable => {
            panic!("memory-safety trust-vc obligations should be import candidates")
        }
        TrustVcNativeTrustIrCertificateImport::Refuted { .. } => panic!(
            "compiler must not promote metadata-only trust-vc proof-unit JSON into a refutation outcome"
        ),
    }
}

#[test]
fn structured_proof_unit_is_deferred_without_minting_native_trust_vc_evidence() {
    let obligation_id = "obligation:demo::borrow:ownership:0";
    let proof_unit = serde_json::json!({
        "source_id": "trust-mir-extract:demo__borrow",
        "unit_id": "demo::borrow",
        "native_context": {
            "function_signature": {
                "name": "demo::borrow",
                "params": [
                    {
                        "name": "ptr_live",
                        "sort": { "kind": "bool" }
                    }
                ],
                "return_sort": { "kind": "bool" }
            },
            "ownership": {
                "places": [
                    {
                        "place": "x",
                        "sort": {
                            "kind": "bit_vector",
                            "width": 32,
                            "signed": false
                        }
                    }
                ],
                "borrows": [
                    {
                        "region": "r0",
                        "place": "x",
                        "kind": "shared"
                    }
                ]
            }
        },
        "obligations": [
            {
                "id": obligation_id,
                "predicate": {
                    "kind": "compare",
                    "op": "eq",
                    "left": {
                        "kind": "variable",
                        "name": "ptr_live",
                        "sort": { "kind": "bool" }
                    },
                    "right": {
                        "kind": "variable",
                        "name": "ptr_live",
                        "sort": { "kind": "bool" }
                    }
                },
                "location": "src/lib.rs:12:9"
            }
        ]
    });
    let mut canonical_proof_unit = String::new();
    write_canonical_json_value(&proof_unit, &mut canonical_proof_unit)
        .expect("direct proof-unit fixture canonicalizes");
    let proof_unit = canonical_proof_unit;
    let public_predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::unary(
            trust_verifier_api::TrustSpecUnaryOp::Not,
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Eq,
                trust_verifier_api::TrustSpecExpr::variable(
                    "ptr_live",
                    trust_verifier_api::TrustSpecSort::Bool,
                ),
                trust_verifier_api::TrustSpecExpr::variable(
                    "ptr_live",
                    trust_verifier_api::TrustSpecSort::Bool,
                ),
            ),
        ),
        vec![trust_verifier_api::TrustSpecVariable {
            name: "ptr_live".to_string(),
            sort: trust_verifier_api::TrustSpecSort::Bool,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
        }],
    );
    public_predicate.validate().expect("public direct-carrier predicate validates");
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: obligation_id.to_string(),
        kind: trust_verifier_api::ObligationKind::Ownership,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "ownership".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SORT_METADATA_KEY.to_string(),
                value: "Bool".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SMTLIB_METADATA_KEY.to_string(),
                value: "(not (= ptr_live ptr_live))".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: "1".repeat(64),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&public_predicate)
                    .expect("public direct-carrier predicate serializes canonically"),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_vc_bridge::TRUST_VC_CONDITION_ORIGIN_METADATA_KEY.to_string(),
                value: trust_vc_bridge::TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_vc_bridge::TRUST_VC_PROOF_OBLIGATION_METADATA_KEY.to_string(),
                value: trust_vc_bridge::TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_vc_bridge::TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY.to_string(),
                value: trust_vc_bridge::TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_vc_bridge::TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY
                    .to_string(),
                value: trust_vc_bridge::TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
                value: proof_unit,
            },
        ],
    };

    match trust_vc_native_trust_ir_certificate_import(&obligation) {
        TrustVcNativeTrustIrCertificateImport::Unavailable { status, reason } => {
            assert_eq!(
                status,
                trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED,
                "unexpected structured-carrier rejection: {reason}"
            );
            assert_eq!(reason, trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON);
        }
        TrustVcNativeTrustIrCertificateImport::Refuted { .. } => {
            panic!("the tautological ownership fixture must not be reported as refuted")
        }
        TrustVcNativeTrustIrCertificateImport::NotApplicable => {
            panic!("ownership trust-vc obligations should be import candidates")
        }
    }
}

fn body_bound_identity_function()
-> (trust_types::VerifiableFunction, trust_types::CompilerContractBundle) {
    body_bound_identity_function_ensuring(
        "result >= x",
        Formula::Ge(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        ),
    )
}

/// `fn body_bound_identity(x: u64) -> u64 ensures <clause> { x }`, with the
/// postcondition supplied by the caller so a FALSE clause can be driven through
/// the identical body-bound machinery. `formula` must be the typed proposition
/// in the compiler's own vocabulary (`_0` for the return place).
fn body_bound_identity_function_ensuring(
    clause: &str,
    formula: Formula,
) -> (trust_types::VerifiableFunction, trust_types::CompilerContractBundle) {
    let span = native_trust_ir_test_span(88);
    let int_ty = trust_types::Ty::Int { width: 64, signed: false };
    let contract = trust_types::Contract {
        kind: trust_types::ContractKind::Ensures,
        span: span.clone(),
        // Match the compiler query's typed proposition exactly: the canonical
        // body retains source-level `result`, while its structural formula
        // names rustc's MIR return place `_0`. The body-bound finalizer is
        // responsible for the digest-gated sibling-vocabulary normalization.
        body: format!("__trust_lowered_compiler_contract__:{clause}"),
    };
    let function = trust_types::VerifiableFunction {
        name: "body_bound_identity".to_string(),
        def_path: "demo::body_bound_identity".to_string(),
        span,
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: int_ty.clone(), name: None },
                trust_types::LocalDecl {
                    index: 1,
                    ty: int_ty.clone(),
                    name: Some("x".to_string()),
                },
            ],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![trust_types::Statement::Assign {
                    place: trust_types::Place::local(0),
                    rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(
                        trust_types::Place::local(1),
                    )),
                    span: native_trust_ir_test_span(89),
                }],
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 1,
            return_ty: int_ty,
        },
        contracts: vec![contract.clone()],
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    };
    let compiler_contracts = trust_types::CompilerContractBundle::new(vec![contract.clone()])
        .with_typed_propositions(vec![trust_types::CompilerContractProposition {
            source_contract_index: 0,
            kind: contract.kind,
            body: contract.body.clone(),
            formula,
            variable_domains: vec![
                trust_types::CompilerContractVariableDomain {
                    name: "_0".to_string(),
                    domain: trust_types::CompilerContractValueDomain::MachineInt {
                        width: 64,
                        signed: false,
                    },
                },
                trust_types::CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: trust_types::CompilerContractValueDomain::MachineInt {
                        width: 64,
                        signed: false,
                    },
                },
            ],
        }]);
    (function, compiler_contracts)
}

#[test]
fn body_bound_finalizer_rejects_any_source_or_synthetic_provenance_key() {
    let (function, compiler_contracts) = body_bound_identity_function();
    let bundle =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &[]);
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::Postcondition)
        .expect("typed Ensures marker");
    let module = trust_ir_bridge::lower_mir_compat_to_trust_ir(&function)
        .expect("identity body lowers to typed TrustIr");
    let function_id = native_trust_ir_function_id(&module, &function)
        .expect("identity function has a unique native id");
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &bundle.contracts,
            obligation,
            &bundle,
            &compiler_contracts,
        )
        .is_some(),
        "unmodified compiler-origin Ensures marker must be body-bindable",
    );

    let mut duplicated_contracts = bundle.contracts.clone();
    duplicated_contracts.push(
        duplicated_contracts
            .iter()
            .find(|contract| Some(&contract.contract_id) == obligation.contract_id.as_ref())
            .expect("linked Ensures contract")
            .clone(),
    );
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &duplicated_contracts,
            obligation,
            &bundle,
            &compiler_contracts,
        )
        .is_none(),
        "a duplicated contract id must be ambiguous rather than selecting the first row",
    );

    let obligation_index = bundle
        .obligations
        .iter()
        .position(|candidate| candidate.obligation_id == obligation.obligation_id)
        .expect("postcondition index");
    let duplicate_binding = PendingNativeTrustIrBinding {
        obligation_index,
        verifier_suite: "trust-wp",
        proof_obligation_id: trust_ir::ProofId::new(0),
    };
    let mut duplicate_binding_bundle = bundle.clone();
    finalize_trust_wp_body_bound_public_claims(
        &module,
        function_id,
        &function,
        &mut duplicate_binding_bundle,
        Some(&bundle),
        Some(&compiler_contracts),
        &[duplicate_binding.clone(), duplicate_binding],
    )
    .expect("ambiguous private bindings fail closed without corrupting the bundle");
    assert_eq!(
        duplicate_binding_bundle.obligations[obligation_index].contract_id, obligation.contract_id,
        "two bindings for one public row must not select body-bound semantics",
    );
    assert!(
        duplicate_binding_bundle
            .contracts
            .iter()
            .all(|contract| { !contract.contract_id.starts_with("contract:trust-wp-body-bound:") })
    );

    for (key, value) in [
        (TRUST_WP_TYPED_FORMULA_SOURCE_METADATA_KEY, "foreign-source-value"),
        (TRUST_WP_TYPED_FORMULA_SYNTHETIC_CONTRACT_METADATA_KEY, "synthetic:one"),
        (TRUST_WP_TYPED_FORMULA_ORIGINAL_CONTRACT_METADATA_KEY, "original:one"),
    ] {
        let mut forged_contracts = bundle.contracts.clone();
        let linked = forged_contracts
            .iter_mut()
            .find(|contract| Some(&contract.contract_id) == obligation.contract_id.as_ref())
            .expect("linked Ensures contract");
        linked.metadata.extend([
            trust_verifier_api::MetadataEntry { key: key.to_string(), value: value.to_string() },
            trust_verifier_api::MetadataEntry { key: key.to_string(), value: value.to_string() },
        ]);
        assert!(
            trust_wp_body_bound_contract_for_obligation(
                &module,
                function_id,
                &function,
                &forged_contracts,
                obligation,
                &bundle,
                &compiler_contracts,
            )
            .is_none(),
            "duplicate/foreign provenance key `{key}` must fail closed",
        );

        let mut forged_obligation = obligation.clone();
        forged_obligation.metadata.extend([
            trust_verifier_api::MetadataEntry { key: key.to_string(), value: value.to_string() },
            trust_verifier_api::MetadataEntry { key: key.to_string(), value: value.to_string() },
        ]);
        assert!(
            trust_wp_body_bound_contract_for_obligation(
                &module,
                function_id,
                &function,
                &bundle.contracts,
                &forged_obligation,
                &bundle,
                &compiler_contracts,
            )
            .is_none(),
            "obligation provenance key `{key}` must fail closed regardless of value/cardinality",
        );
    }

    let typed_digest_entry = bundle.contracts[0]
        .metadata
        .iter()
        .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
        .expect("typed proposition digest")
        .clone();
    let mut duplicate_digest_contracts = bundle.contracts.clone();
    duplicate_digest_contracts[0].metadata.push(typed_digest_entry.clone());
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &duplicate_digest_contracts,
            obligation,
            &bundle,
            &compiler_contracts,
        )
        .is_none(),
        "a duplicated public typed-proposition digest must not authenticate itself",
    );
    let mut mismatched_digest_obligation = obligation.clone();
    mismatched_digest_obligation
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
        .expect("obligation typed proposition digest")
        .value = format!("sha256:{}", "a".repeat(64));
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &bundle.contracts,
            &mismatched_digest_obligation,
            &bundle,
            &compiler_contracts,
        )
        .is_none(),
        "public digest drift must fail against the independent compiler reference",
    );

    let arbitrary_metadata = trust_verifier_api::MetadataEntry {
        key: "trust.body_bound.unowned".to_string(),
        value: "must-not-cross-the-compiler-boundary".to_string(),
    };
    let mut augmented_contracts = bundle.contracts.clone();
    augmented_contracts[0].metadata.push(arbitrary_metadata.clone());
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &augmented_contracts,
            obligation,
            &bundle,
            &compiler_contracts,
        )
        .is_none(),
        "only certified-monitor metadata may augment the compiler contract reference",
    );
    let mut augmented_obligation = obligation.clone();
    augmented_obligation.metadata.push(arbitrary_metadata);
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &bundle.contracts,
            &augmented_obligation,
            &bundle,
            &compiler_contracts,
        )
        .is_none(),
        "only certified-monitor metadata may augment the compiler obligation reference",
    );
}

#[test]
fn body_bound_typed_reference_alias_and_requires_guards_fail_closed() {
    let (function, compiler_contracts) = body_bound_identity_function();
    let carrier_count =
        |function: &trust_types::VerifiableFunction,
         compiler_contracts: &trust_types::CompilerContractBundle| {
            build_full_verification_input_for_tests_with_loop_feedback_and_body_bound_carriers(
                function,
                compiler_contracts,
                &[],
                &[],
            )
            .2
            .len()
        };

    let mut duplicated_typed = compiler_contracts.clone();
    let duplicate_typed_proposition = duplicated_typed.typed_propositions[0].clone();
    duplicated_typed.typed_propositions.push(duplicate_typed_proposition);
    assert_eq!(
        carrier_count(&function, &duplicated_typed),
        0,
        "duplicate private typed propositions must not fall back to source parsing",
    );

    let mut stale_formula = compiler_contracts.clone();
    stale_formula.typed_propositions[0].formula = Formula::Le(
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
        Box::new(Formula::Var("x".to_string(), Sort::Int)),
    );
    assert_eq!(
        carrier_count(&function, &stale_formula),
        0,
        "formula drift in the compiler query must fail closed",
    );

    let mut stale_body = compiler_contracts.clone();
    stale_body.typed_propositions[0].body.push_str(" && true");
    assert_eq!(
        carrier_count(&function, &stale_body),
        0,
        "body drift in the compiler query must fail closed",
    );

    let mut stale_domain = compiler_contracts.clone();
    stale_domain.typed_propositions[0].variable_domains[0].domain =
        trust_types::CompilerContractValueDomain::MachineInt { width: 32, signed: false };
    assert_eq!(
        carrier_count(&function, &stale_domain),
        0,
        "a logical-Int proposition with the wrong source machine domain must fail closed",
    );

    // `_0` is both rustc's return spelling and a legal source argument. A
    // proposition cannot disambiguate the two when an argument has that name.
    let mut colliding_function = function.clone();
    colliding_function.body.locals[1].name = Some("_0".to_string());
    colliding_function.contracts[0].body =
        "__trust_lowered_compiler_contract__:result >= _0".to_string();
    let mut colliding_contracts = compiler_contracts.clone();
    colliding_contracts.contracts[0] = colliding_function.contracts[0].clone();
    colliding_contracts.typed_propositions[0].body = colliding_function.contracts[0].body.clone();
    colliding_contracts.typed_propositions[0].formula = Formula::Ge(
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
    );
    colliding_contracts.typed_propositions[0].variable_domains.truncate(1);
    assert_eq!(
        carrier_count(&colliding_function, &colliding_contracts),
        0,
        "a source argument named `_0` must revoke return-alias normalization",
    );

    let reference =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &[]);
    let obligation = reference
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::Postcondition)
        .expect("typed Ensures marker");
    let module = trust_ir_bridge::lower_mir_compat_to_trust_ir(&function)
        .expect("identity body lowers to typed TrustIr");
    let function_id = native_trust_ir_function_id(&module, &function)
        .expect("identity function has a unique native id");

    let mut mixed_reference = reference.clone();
    let mut mixed_contracts = reference.contracts.clone();
    let trust_verifier_api::ContractPredicate::TrustIr { value, .. } =
        &mut mixed_reference.contracts[0].predicate
    else {
        panic!("typed fixture predicate")
    };
    let mut mixed_predicate: trust_verifier_api::TrustSpecPredicate =
        serde_json::from_value(value.clone()).expect("typed fixture decodes");
    let trust_verifier_api::TrustSpecExprKind::Binary { lhs, .. } = &mut mixed_predicate.root.kind
    else {
        panic!("typed fixture comparison")
    };
    lhs.kind = trust_verifier_api::TrustSpecExprKind::Result;
    *value = serde_json::to_value(mixed_predicate).expect("mixed result predicate serializes");
    mixed_contracts[0].predicate = mixed_reference.contracts[0].predicate.clone();
    assert!(
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            &function,
            &mixed_contracts,
            &mixed_reference.obligations[0],
            &mixed_reference,
            &compiler_contracts,
        )
        .is_none(),
        "an explicit Result node plus the authenticated inferred `_0` alias is ambiguous",
    );

    let rejects_model = |candidate: &trust_types::VerifiableFunction| {
        trust_wp_body_bound_contract_for_obligation(
            &module,
            function_id,
            candidate,
            &reference.contracts,
            obligation,
            &reference,
            &compiler_contracts,
        )
        .is_none()
    };

    let mut duplicate_index = function.clone();
    duplicate_index.body.locals.push(duplicate_index.body.locals[1].clone());
    assert!(rejects_model(&duplicate_index), "all duplicate local indices must fail closed");

    let mut missing_argument = function.clone();
    missing_argument.body.locals.retain(|local| local.index != 1);
    assert!(rejects_model(&missing_argument), "a missing required argument index must fail closed",);

    let mut missing_return = function.clone();
    missing_return.body.locals.retain(|local| local.index != 0);
    assert!(rejects_model(&missing_return), "a missing return index must fail closed",);

    let mut duplicate_name = function.clone();
    duplicate_name.body.arg_count = 2;
    let mut second_arg = duplicate_name.body.locals[1].clone();
    second_arg.index = 2;
    duplicate_name.body.locals.push(second_arg);
    assert!(
        rejects_model(&duplicate_name),
        "distinct argument indices with one name must not be conflated",
    );

    let mut wrong_return_name = function.clone();
    wrong_return_name.body.locals[0].name = Some("not_the_return_spelling".to_string());
    assert!(rejects_model(&wrong_return_name));

    let mut wrong_return_type = function.clone();
    wrong_return_type.body.locals[0].ty = trust_types::Ty::Bool;
    wrong_return_type.body.return_ty = trust_types::Ty::Bool;
    assert!(
        rejects_model(&wrong_return_type),
        "the explicit return type must agree with the proposition and defining expression",
    );

    let requires = trust_types::Contract {
        kind: trust_types::ContractKind::Requires,
        span: function.span.clone(),
        body: "__trust_lowered_compiler_contract__:x >= 0".to_string(),
    };
    let mut requires_function = function.clone();
    requires_function.contracts.push(requires.clone());
    let mut requires_contracts = compiler_contracts.clone();
    requires_contracts.contracts.push(requires.clone());
    requires_contracts.typed_propositions.push(trust_types::CompilerContractProposition {
        source_contract_index: 1,
        kind: requires.kind,
        body: requires.body.clone(),
        formula: Formula::Ge(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        variable_domains: vec![trust_types::CompilerContractVariableDomain {
            name: "x".to_string(),
            domain: trust_types::CompilerContractValueDomain::MachineInt {
                width: 64,
                signed: false,
            },
        }],
    });
    assert_eq!(
        carrier_count(&requires_function, &requires_contracts),
        0,
        "an authored Requires row closes the unconditional body-bound lane",
    );

    // Even deleting the Requires row from the mutable public transport cannot
    // bypass the guard because the raw compiler inventory remains private.
    let compiler_reference =
        trust_mir_extract::contract_bundle_to_verifier_api(&requires_function, &requires_contracts);
    let mut deleted_public_requires = trust_mir_extract::function_to_verifier_api_bundle(
        &requires_function,
        &requires_contracts,
        &[],
    );
    deleted_public_requires
        .contracts
        .retain(|contract| contract.kind != trust_verifier_api::ContractKind::Requires);
    deleted_public_requires
        .obligations
        .retain(|obligation| obligation.kind != trust_verifier_api::ObligationKind::Precondition);
    let mut deleted_carriers = Vec::new();
    build_native_trust_ir_bundle_for_test_verifier_api_with_carriers(
        &requires_function,
        &mut deleted_public_requires,
        Some(&compiler_reference),
        Some(&requires_contracts),
        &mut deleted_carriers,
        &[],
    )
    .expect("public deletion fixture still builds a native bundle");
    assert!(deleted_carriers.is_empty());
}

#[test]
fn body_bound_result_alias_rewrite_changes_only_exact_variable_nodes() {
    let mut value = serde_json::json!({
        "exact": { "var": "_0" },
        "larger": { "var": "_0", "sort": "int" },
        "_0": { "literal": "_0" },
        "string": "_0",
        "array": [
            { "var": "x" },
            { "nested": { "var": "_0" } }
        ]
    });
    assert_eq!(rewrite_body_bound_result_alias(&mut value, "_0"), 2);
    assert_eq!(value["exact"]["var"], "result");
    assert_eq!(value["array"][1]["nested"]["var"], "result");
    assert_eq!(value["larger"]["var"], "_0");
    assert_eq!(value["_0"]["literal"], "_0");
    assert_eq!(value["string"], "_0");
    assert_eq!(value["array"][0]["var"], "x");
}

#[test]
fn body_bound_monitor_stamped_ge_and_gt_preserve_exact_compiler_carriers() {
    let build = |function: &trust_types::VerifiableFunction,
                 compiler_contracts: &trust_types::CompilerContractBundle| {
        let reference =
            trust_mir_extract::contract_bundle_to_verifier_api(function, compiler_contracts);
        let mut bundle =
            trust_mir_extract::function_to_verifier_api_bundle(function, compiler_contracts, &[]);
        let original_metadata_len = bundle.contracts[0].metadata.len();
        stamp_certified_monitor_metadata_from_records(
            &[],
            &monitor_reference_function(&reference),
            &reference,
            &mut bundle,
        );
        assert!(
            bundle.contracts[0].metadata.len() > original_metadata_len,
            "the parity fixture must exercise post-reference monitor augmentation",
        );
        let mut carriers = Vec::new();
        let native = build_native_trust_ir_bundle_for_test_verifier_api_with_carriers(
            function,
            &mut bundle,
            Some(&reference),
            Some(compiler_contracts),
            &mut carriers,
            &[],
        )
        .expect("monitor-stamped body-bound native construction")
        .expect("the postcondition requests native TrustIr");
        (bundle, native, carriers)
    };

    let (ge_function, ge_contracts) = body_bound_identity_function();
    assert!(ge_function.body.locals[0].name.is_none(), "match production return-local naming");
    let (ge_bundle, ge_native, ge_carriers) = build(&ge_function, &ge_contracts);
    assert_eq!(ge_carriers.len(), 1);
    let ge_contract = ge_bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id.starts_with("contract:trust-wp-body-bound:"))
        .expect("monitor-stamped Ge gets a derived body-bound contract");
    let trust_verifier_api::ContractPredicate::CanonicalJson { value, .. } = &ge_contract.predicate
    else {
        panic!("derived Ge predicate must be canonical JSON")
    };
    assert_eq!(value["body"]["op"], "let");
    assert_eq!(value["body"]["value"]["var"], "x");

    let ge_live = verify_full_bundle_with_body_bound_receipts(
        &ge_bundle,
        &full_verification_dispatched_obligations(
            &ge_bundle,
            &ExactDefinitionEntryMarkerSet::default(),
        ),
        Some(&ge_native),
        &ge_carriers,
        &trust_router::VerifierExecutionContext::new("body-bound-monitor-ge"),
    );
    assert_eq!(ge_live.body_bound_receipts.len(), 1);

    let mut gt_function = ge_function.clone();
    gt_function.contracts[0].body = "__trust_lowered_compiler_contract__:result > x".to_string();
    let mut gt_contracts = ge_contracts.clone();
    gt_contracts.contracts[0] = gt_function.contracts[0].clone();
    gt_contracts.typed_propositions[0].body = gt_function.contracts[0].body.clone();
    gt_contracts.typed_propositions[0].formula = Formula::Gt(
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
        Box::new(Formula::Var("x".to_string(), Sort::Int)),
    );
    let (gt_bundle, gt_native, gt_carriers) = build(&gt_function, &gt_contracts);
    assert_eq!(
        gt_carriers.len(),
        1,
        "a false body-bound claim still needs the exact carrier so native replay can refute it",
    );
    let gt_target = &gt_carriers[0].canonical_obligation.obligation_id;
    let gt_live = verify_full_bundle_with_body_bound_receipts(
        &gt_bundle,
        &full_verification_dispatched_obligations(
            &gt_bundle,
            &ExactDefinitionEntryMarkerSet::default(),
        ),
        Some(&gt_native),
        &gt_carriers,
        &trust_router::VerifierExecutionContext::new("body-bound-monitor-gt"),
    );
    assert!(gt_live.body_bound_receipts.is_empty(), "refutations never mint proof receipts");
    assert!(gt_live.result.evidence.iter().any(|evidence| {
        evidence.obligation_id == *gt_target
            && evidence.status == trust_verifier_api::EvidenceStatus::Failed
    }));
}

#[test]
fn body_bound_finalizer_digest_and_returned_carrier_have_one_exact_identity() {
    let (function, compiler_contracts) = body_bound_identity_function();
    let (bundle, native_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &[]);
    let native_bundle = native_bundle
        .expect("body-bound native bundle construction")
        .expect("body-bound postcondition requests native TrustIr");
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::Postcondition)
        .expect("finalized body-bound postcondition");
    let contract_id = obligation.contract_id.as_deref().expect("finalized contract link");
    assert!(contract_id.starts_with("contract:trust-wp-body-bound:"));
    let contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == contract_id)
        .expect("body-bound derived public contract");
    assert!(contract.metadata.iter().any(|entry| {
        entry.key == TRUST_WP_TYPED_FORMULA_SOURCE_METADATA_KEY
            && entry.value == TRUST_WP_TYPED_FORMULA_SOURCE_BODY_BOUND_VALUE
    }));
    let trust_verifier_api::ContractPredicate::CanonicalJson { schema, value } =
        &contract.predicate
    else {
        panic!("body-bound contract must carry the canonical sibling formula")
    };
    assert_eq!(schema, TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION);
    assert_eq!(value["body"]["op"], "let");
    assert_eq!(value["body"]["name"], "result");
    assert_eq!(value["body"]["value"]["var"], "x");

    let proof_id = test_obligation_metadata(
        obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .parse::<u32>()
    .map(trust_ir::ProofId::new)
    .expect("body-bound native proof id");
    let native_obligation = native_bundle
        .module
        .proof_obligations
        .iter()
        .find(|candidate| candidate.id == proof_id)
        .expect("body-bound native proof obligation");
    let embedded_public = native_obligation
        .source
        .as_ref()
        .and_then(|source| source.public.as_ref())
        .expect("native proof source embeds the public identity");
    let semantic_digest = bundle
        .canonical_obligation_semantic_digest_sha256(obligation)
        .expect("finalized public semantic digest");
    assert_eq!(embedded_public.obligation_id, obligation.obligation_id);
    assert_eq!(
        embedded_public.semantic_digest,
        trust_ir_sha256_digest_from_hex(&semantic_digest, &obligation.obligation_id)
            .expect("semantic digest decodes"),
        "the native proof must commit the post-finalizer public semantics",
    );

    let evidence = unsupported_evidence_for(obligation);
    let run = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("body-bound-carrier-test").snapshot(),
        &bundle,
        evidence.engine.clone(),
        std::slice::from_ref(obligation),
        vec![evidence],
    );
    let mut vc = test_vc(88);
    vc.kind = VcKind::Postcondition;
    vc.function = trust_types::Symbol::intern(&function.def_path);
    let binding = result_obligation_binding(0, &vc, obligation)
        .expect("finalized public row has an exact private carrier binding");
    let returned = run.requested_obligations.first().expect("returned public carrier");
    assert!(binding.matches_public_obligation(returned));

    let mut mutated = returned.clone();
    mutated.contract_id = Some("contract:trust-wp-body-bound:mutated".to_string());
    assert!(
        !binding.matches_public_obligation(&mutated),
        "a post-dispatch contract-link mutation must revoke the returned carrier",
    );
}

#[test]
fn body_bound_live_trust_wp_receipt_is_exact_private_authority() {
    let (function, compiler_contracts) = body_bound_identity_function();
    let (bundle, native_bundle, carriers) =
        build_full_verification_input_for_tests_with_loop_feedback_and_body_bound_carriers(
            &function,
            &compiler_contracts,
            &[],
            &[],
        );
    let native_bundle = native_bundle
        .expect("body-bound native bundle construction")
        .expect("body-bound postcondition requests native TrustIr");
    assert_eq!(carriers.len(), 1, "the exact body-bound row must have one compiler carrier");

    let dispatched = full_verification_dispatched_obligations(
        &bundle,
        &ExactDefinitionEntryMarkerSet::default(),
    );
    let context = trust_router::VerifierExecutionContext::new("body-bound-live-receipt-test");
    let live = verify_full_bundle_with_body_bound_receipts(
        &bundle,
        &dispatched,
        Some(&native_bundle),
        &carriers,
        &context,
    );
    assert_eq!(
        live.body_bound_receipts.len(),
        1,
        "the real Trust-WP dispatch must seal one exact body-bound proof: {:#?}",
        live.result,
    );

    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &[],
        live.result.context.clone(),
    );
    let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &live.result,
        &[],
        &snapshot,
    );
    keep_exact_source_clause_markers_pending(&bundle, &mut results, &bindings);
    let marker_id = &carriers[0].canonical_obligation.obligation_id;
    let marker_index = bindings
        .iter()
        .position(|binding| {
            binding.as_ref().is_some_and(|binding| binding.public_obligation_id == *marker_id)
        })
        .expect("body-bound marker result row");
    assert!(matches!(results[marker_index].0.formula, Formula::Bool(false)));
    assert!(matches!(results[marker_index].1, VerificationResult::Unknown { .. }));

    // Even this valid, canonical public Proved run is attribution only. The
    // generic authority builder must not recreate a native capability from it.
    let cleancic = vec![None; results.len()];
    let no_revalidations = vec![None; results.len()];
    let mut authorities = build_result_proof_authorities_with_revalidations(
        &results,
        &bindings,
        Some(&live.result),
        &cleancic,
        &no_revalidations,
    );
    assert!(authorities.iter().all(Option::is_none));

    let mut public_only_results = results.clone();
    let mut public_only_authorities = authorities.clone();
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &live.result,
            &[],
            &mut public_only_results,
            &bindings,
            &mut public_only_authorities,
        ),
        0,
        "public run/evidence/manifest data alone must never mint compiler authority",
    );
    assert!(matches!(public_only_results[marker_index].1, VerificationResult::Unknown { .. }));

    let mut tampered_initial_receipts = live.body_bound_receipts.clone();
    tampered_initial_receipts[0]
        .manifest_decision
        .diagnostics
        .push("post-dispatch mutation".to_string());
    assert!(
        finalize_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &live.result,
            &live.result,
            &tampered_initial_receipts,
        )
        .is_empty(),
        "mutating an accepted manifest decision must revoke the private receipt",
    );

    let mut alternate_run = live.result.clone();
    alternate_run.run_id = "body-bound-alternate-run".to_string();
    alternate_run.context.run_id = alternate_run.run_id.clone();
    alternate_run
        .try_reconcile_derived_state()
        .expect("the alternate run identity remains a canonical public envelope");
    assert_ne!(
        alternate_run.try_to_manifest().expect("alternate manifest"),
        live.body_bound_receipts[0].run_manifest,
    );
    assert!(
        finalize_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &alternate_run,
            &alternate_run,
            &live.body_bound_receipts,
        )
        .is_empty(),
        "a separately rebuilt canonical run must not replay the live receipt",
    );

    // Model the production order: an unrelated compiler-owned publication may
    // legitimately change the final manifest after the live receipt was
    // captured, but the exact body-bound target must remain untouched.
    let mut final_run = live.result.clone();
    let unrelated = final_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id != *marker_id)
        .expect("fixture includes an unrelated default-function evidence row");
    unrelated.diagnostics.push("compiler-owned unrelated bridge publication".to_string());
    final_run
        .try_reconcile_derived_state()
        .expect("compiler-owned final publication remains canonical");
    assert_ne!(
        final_run.try_to_manifest().expect("final publication manifest"),
        live.body_bound_receipts[0].run_manifest,
    );
    let finalized_receipts = finalize_body_bound_native_replay_receipts(
        &bundle,
        Some(&native_bundle),
        &live.result,
        &final_run,
        &live.body_bound_receipts,
    );
    assert_eq!(finalized_receipts.len(), 1);

    let mut changed_target_run = final_run.clone();
    changed_target_run
        .evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == *marker_id)
        .expect("body-bound target evidence")
        .diagnostics
        .push("target mutation before final seal".to_string());
    changed_target_run
        .try_reconcile_derived_state()
        .expect("changed-target envelope remains publicly canonical");
    assert!(
        finalize_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &live.result,
            &changed_target_run,
            &live.body_bound_receipts,
        )
        .is_empty(),
        "the second-stage seal must reject any changed target evidence",
    );

    let mut post_seal_mutation = final_run.clone();
    post_seal_mutation.diagnostics.push("mutation after final sealing".to_string());
    post_seal_mutation
        .try_reconcile_derived_state()
        .expect("post-seal mutation remains a canonical public run");
    let mut post_seal_results = results.clone();
    let mut post_seal_authorities = authorities.clone();
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &post_seal_mutation,
            &finalized_receipts,
            &mut post_seal_results,
            &bindings,
            &mut post_seal_authorities,
        ),
        0,
        "any manifest mutation after the second-stage seal must revoke authority",
    );

    let duplicate_receipts = vec![finalized_receipts[0].clone(), finalized_receipts[0].clone()];
    let mut duplicate_results = results.clone();
    let mut duplicate_authorities = authorities.clone();
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &final_run,
            &duplicate_receipts,
            &mut duplicate_results,
            &bindings,
            &mut duplicate_authorities,
        ),
        0,
        "duplicate private receipts are ambiguous and must fail closed as a set",
    );

    let mut refuted_results = results.clone();
    refuted_results[marker_index].1 = failed_test_result();
    let mut refuted_authorities = authorities.clone();
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &final_run,
            &finalized_receipts,
            &mut refuted_results,
            &bindings,
            &mut refuted_authorities,
        ),
        0,
        "a refutation must dominate and can never be overwritten by a receipt",
    );
    assert!(matches!(refuted_results[marker_index].1, VerificationResult::Failed { .. }));

    let mut stale_results = results.clone();
    stale_results[marker_index].0.formula = Formula::Bool(true);
    let mut stale_authorities = authorities.clone();
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &final_run,
            &finalized_receipts,
            &mut stale_results,
            &bindings,
            &mut stale_authorities,
        ),
        0,
        "a changed current row must revoke its exact binding and receipt",
    );

    let mut changed_native_bundle = native_bundle.clone();
    changed_native_bundle.trust_ir_module_digest = trust_ir::ProofDigest::sha256([0x42; 32]);
    let mut changed_native_results = results.clone();
    let mut changed_native_authorities = authorities.clone();
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&changed_native_bundle),
            &final_run,
            &finalized_receipts,
            &mut changed_native_results,
            &bindings,
            &mut changed_native_authorities,
        ),
        0,
        "a changed native module digest must revoke the compiler carrier",
    );

    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &final_run,
            &finalized_receipts,
            &mut results,
            &bindings,
            &mut authorities,
        ),
        1,
    );
    // `ensures result >= x { x }` substitutes to `x <= x`, which the Clean
    // kernel re-derives from the compiler's own pinned claim envelope. The row
    // therefore leaves the trusted replay lane entirely: what carries it is a
    // kernel-checked CIC term, not trust-wp's answer.
    assert!(matches!(
        authorities[marker_index].as_ref(),
        Some(ResultProofAuthority::BodyBoundKernelCertified { .. })
    ));
    assert!(results[marker_index].1.is_proved());
    assert_eq!(
        trust_disposition_for_authority(
            authorities[marker_index].as_ref(),
            marker_index,
            &results[marker_index].0,
            &results[marker_index].1,
            bindings[marker_index].as_ref(),
        ),
        Some((TrustStatus::Certified, TrustProofStrength::Constructive)),
    );
    assert!(
        matches!(
            authorities[marker_index].as_ref().and_then(|authority| authority.kernel_evidence_for(
                marker_index,
                &results[marker_index].0,
                bindings[marker_index].as_ref(),
            )),
            Some(trust_ir::ProofEvidence::CleanCic { .. })
        ),
        "a Certified body-bound row must ship the proof term a consumer re-checks",
    );
}

/// RED, at the compiler seam: a genuine live receipt carrying a FORGED claim.
///
/// The whole receipt discipline is intact — real dispatch, real carrier, real
/// row — and only the pinned claim envelope is rewritten from `result >= x` to
/// the false `result > x`. Certification must fail, because the kernel has no
/// proof of `x < x`, and the honest sibling in the same test must still succeed
/// so the refusal is known to discriminate the claim rather than the shape.
///
/// (The forged receipt could never reach the mint site anyway — its carrier no
/// longer matches the bundle — which is asserted at the end. This test is about
/// the layer BELOW that: the kernel gate holding on its own.)
#[test]
fn body_bound_forged_claim_is_rejected_by_the_kernel() {
    let (function, compiler_contracts) = body_bound_identity_function();
    let (bundle, native_bundle, carriers) =
        build_full_verification_input_for_tests_with_loop_feedback_and_body_bound_carriers(
            &function,
            &compiler_contracts,
            &[],
            &[],
        );
    let native_bundle = native_bundle
        .expect("body-bound native bundle construction")
        .expect("body-bound postcondition requests native TrustIr");

    let dispatched = full_verification_dispatched_obligations(
        &bundle,
        &ExactDefinitionEntryMarkerSet::default(),
    );
    let context = trust_router::VerifierExecutionContext::new("body-bound-forged-claim");
    let live = verify_full_bundle_with_body_bound_receipts(
        &bundle,
        &dispatched,
        Some(&native_bundle),
        &carriers,
        &context,
    );
    let finalized = finalize_body_bound_native_replay_receipts(
        &bundle,
        Some(&native_bundle),
        &live.result,
        &live.result,
        &live.body_bound_receipts,
    );
    assert_eq!(finalized.len(), 1, "the real dispatch must seal one body-bound receipt");

    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &[],
        live.result.context.clone(),
    );
    let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &live.result,
        &[],
        &snapshot,
    );
    keep_exact_source_clause_markers_pending(&bundle, &mut results, &bindings);
    let marker_id = &carriers[0].canonical_obligation.obligation_id;
    let marker_index = bindings
        .iter()
        .position(|binding| {
            binding.as_ref().is_some_and(|binding| binding.public_obligation_id == *marker_id)
        })
        .expect("body-bound marker result row");
    let row = exact_result_row_identity(marker_index, &results[marker_index].0)
        .expect("marker row identity");

    assert!(
        body_bound_kernel_certificate(&finalized[0], &row).is_some(),
        "the honest `result >= x` claim must certify, or the refusal below proves nothing",
    );

    let mut forged = finalized[0].clone();
    let formula = forged
        .live
        .carrier
        .native_proof_obligation
        .formula
        .as_mut()
        .expect("the body-bound carrier pins a native proof formula");
    let honest = formula.payload.clone();
    formula.payload = honest.replace("\"ge\"", "\"gt\"");
    assert_ne!(formula.payload, honest, "the forgery must actually change the claim");
    assert!(
        body_bound_kernel_certificate(&forged, &row).is_none(),
        "`x < x` has no kernel proof, so a forged claim must not certify",
    );

    let mut forged_results = results.clone();
    let mut forged_authorities = vec![None; results.len()];
    assert_eq!(
        apply_body_bound_native_replay_receipts(
            &bundle,
            Some(&native_bundle),
            &live.result,
            &[forged],
            &mut forged_results,
            &bindings,
            &mut forged_authorities,
        ),
        0,
        "a receipt whose carrier no longer matches the bundle mints nothing at all",
    );
}

// Trust (P1.2): a compiler-generated body-aware postcondition VC — a
// `Postcondition` obligation carrying a typed `TrustSpecPredicate` formula
// payload (`trust.vc.formula.payload`) — is deliberately routed to trust-mc's
// typed-CHC/PDR runner, NOT trust-wp: the payload encodes `¬postcond ∧
// body_defs`, a closed CHC error-reachability query that trust-wp's native
// pure replay (a constant folder) cannot discharge. Claim-based
// postconditions (no payload) keep the trust-wp deductive route; see
// `native_trust_ir_route_for_api_obligation`.
#[test]
fn generated_postcondition_vc_gets_typed_chc_contract_and_native_replay_formula() {
    let (function, _, _) = native_trust_ir_compiler_function();
    // Error-reachability form of `#[ensures(amount >= 0)]`: the error relation
    // is reachable iff `amount < 0`. A supported int/bool CHC fragment (not a
    // literal `true`), so the typed-CHC lowering must succeed.
    let int_sort = trust_verifier_api::TrustSpecSort::Int;
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::Lt,
            trust_verifier_api::TrustSpecExpr::variable("amount", int_sort),
            trust_verifier_api::TrustSpecExpr::int_literal("0"),
        ),
        vec![trust_verifier_api::TrustSpecVariable {
            name: "amount".to_string(),
            sort: int_sort,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Local { index: 1 },
        }],
    );
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-generated-postcondition-vc",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: "vc:checked_transfer:postcondition:99".to_string(),
        kind: trust_verifier_api::ObligationKind::Postcondition,
        contract_id: None,
        proof_item_id: None,
        source: native_trust_ir_test_source_location(99),
        description: "postcondition VC generated from MIR".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate)
                    .expect("TrustSpecPredicate should serialize"),
            },
        ],
    });

    let native_trust_ir_bundle =
        build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
            .expect("native TrustIr bundle should build")
            .expect("generated postcondition VC should request native TrustIr");
    assert_eq!(
        native_trust_ir_bundle.trust_ir_module_digest,
        native_trust_ir_bundle.module.stable_digest(),
        "the bundle must mint every authority identity from the module after public claims are finalized"
    );
    native_trust_ir_bundle
        .validate()
        .expect("the final module, lineage, request, and replay identities must agree");
    let obligation = &bundle.obligations[0];
    // P1.2 routing pin: the body-aware postcondition VC must land on trust-mc.
    assert_native_proof_unit_metadata(obligation, "trust-mc");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY,
        ),
        "supported"
    );
    let synthetic_contract_id = test_obligation_metadata(
        obligation,
        super::TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY,
    );
    let public_contract_id = obligation
        .contract_id
        .as_deref()
        .expect("supported trust-mc lowering must link a canonical public semantic contract");
    assert_ne!(public_contract_id, synthetic_contract_id);
    let public_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == public_contract_id)
        .expect("canonical trust-mc public contract should be appended before native bundling");
    let trust_verifier_api::ContractPredicate::MathIr { value: public_value, .. } =
        &public_contract.predicate
    else {
        panic!("canonical trust-mc public contract should carry typed MathIr CHC input");
    };
    assert_eq!(public_value["obligation_id"], obligation.obligation_id);
    assert!(public_value.get("native_metadata").is_none());

    let synthetic_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == synthetic_contract_id)
        .expect("synthetic typed trust-mc CHC contract should be appended");
    let trust_verifier_api::ContractPredicate::MathIr { schema, value } =
        &synthetic_contract.predicate
    else {
        panic!("synthetic trust-mc contract should carry typed MathIr CHC input");
    };
    assert_eq!(schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    assert_eq!(value["schema_version"], super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    // A supported lowering must emit a REAL mir-derived CHC query, not the
    // fail-closed `router_placeholder` used for unsupported payloads.
    assert_eq!(value["origin"], "mir_derived");
    assert!(value.get("unsupported").is_none());
    assert_eq!(value["query"]["target"], "error");
    assert_eq!(value["vars"], serde_json::json!([{ "name": "amount", "sort": { "kind": "int" } }]));
    let constraint = &value["rules"][0]["body"]["constraints"][0];
    assert_eq!(constraint["kind"], "binary");
    assert_eq!(constraint["op"], "lt");
    assert!(
        value["obligation_id"]
            .as_str()
            .is_some_and(|id| id.starts_with("trust_ir-native-trust_mc-request-"))
    );
    assert_eq!(
        synthetic_contract
            .metadata
            .iter()
            .find(|entry| entry.key == "trust-trust-mc.typed-chc-obligation.source")
            .map(|entry| entry.value.as_str()),
        Some("compiler-native-trust-ir-trust-spec-vc")
    );

    let proof_obligation_id = test_obligation_metadata(
        obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .parse::<u32>()
    .map(trust_ir::ProofId::new)
    .expect("trust-mc proof obligation id should parse");
    let module_obligation = native_trust_ir_bundle
        .module
        .proof_obligations
        .iter()
        .find(|candidate| candidate.id == proof_obligation_id)
        .expect("the final module must contain the public proof obligation");
    let embedded_source = module_obligation
        .source
        .as_ref()
        .expect("the final module must embed exact public source authority");
    assert_eq!(embedded_source.source_id, public_contract_id);
    assert_eq!(module_obligation.function, Some(trust_ir::FuncId::new(0)));
    let embedded_public = embedded_source
        .public
        .as_ref()
        .expect("the final module must embed an atomic public identity");
    assert_eq!(embedded_public.obligation_id, obligation.obligation_id);
    let expected_public_digest = bundle
        .canonical_obligation_semantic_digest_sha256(obligation)
        .expect("public semantic digest should remain canonical after transport annotation");
    assert_eq!(
        embedded_public.semantic_digest,
        trust_ir_sha256_digest_from_hex(&expected_public_digest, &obligation.obligation_id)
            .expect("canonical public digest should decode as SHA-256")
    );
    let embedded_range = embedded_source.range.expect("public source range must be present");
    assert_eq!(native_trust_ir_bundle.module.file_name(embedded_range.file), Some("src/lib.rs"));
    assert_eq!((embedded_range.start_line, embedded_range.start_col), (99, 1));
    assert_eq!((embedded_range.end_line, embedded_range.end_col), (99, 20));
    let compiler_source = native_trust_ir_bundle
        .obligation_source(proof_obligation_id)
        .expect("compiler facts must project the embedded source identity");
    assert_eq!(compiler_source.public_obligation_id, obligation.obligation_id);
    assert_eq!(compiler_source.function, module_obligation.function);
    assert_eq!(
        compiler_source.assertion_id,
        Some(trust_ir::NativeAssertionId::new(trust_types::stable_u32_id(
            embedded_source.assertion_id.as_bytes()
        )))
    );
    assert_eq!(
        compiler_source.span,
        Some(trust_ir::SourceSpan {
            file: embedded_range.file,
            line: embedded_range.start_line,
            col: embedded_range.start_col,
        })
    );
    let request = native_trust_ir_bundle
        .requests
        .iter()
        .find(|request| {
            matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustMc)
                && request.obligations().contains(&proof_obligation_id)
        })
        .expect("native bundle should include a trust-mc request for the VC");
    let trust_ir::NativeVerificationRequest::TrustMc(request) = request else {
        panic!("trust-mc request should have the trust-mc variant");
    };
    let atom = request
        .provenance
        .replay_context
        .atoms
        .iter()
        .find(|atom| {
            atom.kind == trust_ir::NativeReplayAtomKind::Assertion
                && atom.obligation == Some(proof_obligation_id)
        })
        .expect("trust-mc replay context should bind the generated proof obligation");
    let module_formula = module_obligation
        .formula
        .as_ref()
        .expect("the final module must carry the same generated proof claim");
    assert_eq!(&atom.formula, module_formula);
    // Native replay formula: the typed TrustSpec predicate rides the replay
    // atom unchanged, digest-bound.
    assert_eq!(atom.formula.schema, trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION);
    let atom_predicate: trust_verifier_api::TrustSpecPredicate =
        serde_json::from_str(&atom.formula.payload).expect("atom payload should parse");
    assert_eq!(atom_predicate, predicate);
    assert_eq!(atom.payload_digest, atom.expected_payload_digest());
}

// Trust (P1.2 precedent, extended to preconditions): a compiler-generated
// call-site precondition VC — a `Precondition` obligation carrying a typed
// `TrustSpecPredicate` formula payload (`trust.vc.formula.payload`) — routes
// to trust-mc's typed-CHC/PDR runner exactly like the P1.2 postcondition arm:
// the payload is a closed CHC error-reachability query over the body relation
// that trust-wp's native pure replay (a constant folder) cannot discharge.
// Preconditions WITHOUT a payload keep the trust-wp deductive route; see
// `native_trust_ir_route_for_api_obligation`.
//
// PRODUCTION-ORDERING FIDELITY: the fixture pre-attaches NO metadata. The VC
// enters as a raw `VcKind::Precondition { callee }` + `Formula` and flows
// through the real `function_to_verifier_api_bundle` (trust-mir-extract), which
// attaches `trust.vc.formula.payload` at obligation CONSTRUCTION — before the
// native TrustIr builder routes it. The route must fire on that real sequence.
#[test]
fn generated_precondition_vc_gets_typed_chc_contract_and_native_replay_formula() {
    let (function, compiler_contracts, _) = native_trust_ir_compiler_function();
    // Error-reachability form of a call-site `#[requires(amount >= 0)]`: the
    // error relation is reachable iff `amount < 0`. A supported int/bool CHC
    // fragment (not a literal `true`), so the typed-CHC lowering must succeed.
    // `callee != function.name`, so the def-site Bool(false) bookkeeping
    // exclusion in `function_to_verifier_api_bundle` does not apply.
    let vcs = vec![VerificationCondition {
        kind: VcKind::Precondition { callee: "demo::validate_amount".to_string() },
        function: trust_types::Symbol::intern("demo::checked_transfer"),
        location: native_trust_ir_test_span(12),
        formula: trust_types::Formula::Lt(
            Box::new(trust_types::Formula::Var("amount".to_string(), trust_types::Sort::Int)),
            Box::new(trust_types::Formula::Int(0)),
        ),
        contract_metadata: None,
    }];

    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("generated precondition VC should request native TrustIr");
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == "vc:demo__checked_transfer:precondition:0")
        .expect("extract should emit the call-site precondition VC obligation");
    assert_eq!(obligation.kind, trust_verifier_api::ObligationKind::Precondition);
    // The typed payload was attached by the REAL extract lowering (not by this
    // fixture) before routing ran.
    let predicate: trust_verifier_api::TrustSpecPredicate = serde_json::from_str(
        test_obligation_metadata(obligation, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY),
    )
    .expect("extract-attached payload should parse");
    assert_eq!(
        predicate,
        trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Lt,
                trust_verifier_api::TrustSpecExpr::variable(
                    "amount",
                    trust_verifier_api::TrustSpecSort::Int
                ),
                trust_verifier_api::TrustSpecExpr::int_literal("0"),
            ),
            vec![trust_verifier_api::TrustSpecVariable {
                name: "amount".to_string(),
                sort: trust_verifier_api::TrustSpecSort::Int,
                origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
            }],
        )
    );
    // Routing pin: the payload-carrying precondition VC must land on trust-mc.
    assert_native_proof_unit_metadata(obligation, "trust-mc");
    assert_eq!(
        test_obligation_metadata(
            obligation,
            super::TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY,
        ),
        "supported"
    );
    let synthetic_contract_id = test_obligation_metadata(
        obligation,
        super::TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY,
    );
    let public_contract_id = obligation
        .contract_id
        .as_deref()
        .expect("supported trust-mc lowering must link a canonical public semantic contract");
    assert_ne!(public_contract_id, synthetic_contract_id);
    let public_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == public_contract_id)
        .expect("canonical trust-mc public contract should be appended before native bundling");
    let trust_verifier_api::ContractPredicate::MathIr { value: public_value, .. } =
        &public_contract.predicate
    else {
        panic!("canonical trust-mc public contract should carry typed MathIr CHC input");
    };
    assert_eq!(public_value["obligation_id"], obligation.obligation_id);
    assert!(public_value.get("native_metadata").is_none());

    let synthetic_contract = bundle
        .contracts
        .iter()
        .find(|contract| contract.contract_id == synthetic_contract_id)
        .expect("synthetic typed trust-mc CHC contract should be appended");
    let trust_verifier_api::ContractPredicate::MathIr { schema, value } =
        &synthetic_contract.predicate
    else {
        panic!("synthetic trust-mc contract should carry typed MathIr CHC input");
    };
    assert_eq!(schema, super::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA);
    // A supported lowering must emit a REAL mir-derived CHC query, not the
    // fail-closed `router_placeholder` used for unsupported payloads.
    assert_eq!(value["origin"], "mir_derived");
    assert!(value.get("unsupported").is_none());
    assert_eq!(value["query"]["target"], "error");

    let proof_obligation_id = test_obligation_metadata(
        obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .parse::<u32>()
    .map(trust_ir::ProofId::new)
    .expect("trust-mc proof obligation id should parse");
    let request = native_trust_ir_bundle
        .requests
        .iter()
        .find(|request| {
            matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustMc)
                && request.obligations().contains(&proof_obligation_id)
        })
        .expect("native bundle should include a trust-mc request for the VC");
    let trust_ir::NativeVerificationRequest::TrustMc(request) = request else {
        panic!("trust-mc request should have the trust-mc variant");
    };
    let atom = request
        .provenance
        .replay_context
        .atoms
        .iter()
        .find(|atom| {
            atom.kind == trust_ir::NativeReplayAtomKind::Assertion
                && atom.obligation == Some(proof_obligation_id)
        })
        .expect("trust-mc replay context should bind the generated proof obligation");
    assert_eq!(atom.formula.schema, trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION);
    let atom_predicate: trust_verifier_api::TrustSpecPredicate =
        serde_json::from_str(&atom.formula.payload).expect("atom payload should parse");
    assert_eq!(atom_predicate, predicate);
}

// Fail-closed pin for the P1.2-extension route arm: a Precondition WITHOUT a
// typed formula payload (e.g. the def-site `#[requires]` marker, contract_id
// Some, origin Contract) keeps trust-wp's deductive route — the status quo.
#[test]
fn precondition_without_typed_payload_keeps_trust_wp_route() {
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "trust-obligation:demo::f:precondition:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Precondition,
        contract_id: Some("trust-contract:demo::f:requires:0".to_string()),
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "prove requires contract".to_string(),
        required_strength: Some(trust_verifier_api::ProofStrength::deductive()),
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };
    assert_eq!(
        native_trust_ir_route_for_api_obligation(&obligation),
        Some(("trust-wp", trust_ir::ObligationKind::Precondition))
    );
}

#[test]
fn trust_wp_proof_context_preserves_replay_assumptions() {
    let (function, compiler_contracts, vcs) = native_trust_ir_compiler_function();
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let mut native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("postcondition and arithmetic-safety obligations require native TrustIr");
    let trust_wp_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.kind == trust_verifier_api::ObligationKind::Postcondition)
        .expect("trust-wp postcondition obligation should be present");
    let proof_obligation_id = test_obligation_metadata(
        trust_wp_obligation,
        trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .parse::<u32>()
    .map(trust_ir::ProofId::new)
    .expect("trust-wp proof obligation id should parse");

    let request = native_trust_ir_bundle
        .requests
        .iter_mut()
        .find(|request| matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustWp))
        .expect("native bundle should include a trust-wp request");
    let trust_ir::NativeVerificationRequest::TrustWp(request) = request else {
        panic!("trust-wp request should have the trust-wp variant");
    };
    request.provenance.replay_context.atoms.push(
        trust_ir::NativeReplayAtom::assumption(
            trust_ir::NativeReplayAtomId::new(99),
            trust_ir::ProofFormula::new("TrustWpPureExprV1", "true"),
        )
        .with_obligation(proof_obligation_id),
    );

    let request = native_trust_ir_bundle
        .requests
        .iter()
        .find(|request| matches!(request.verifier_suite(), trust_ir::NativeVerifierSuite::TrustWp))
        .expect("native bundle should include a trust-wp request");
    let entry = trust_wp_typed_pure_expr_proof_context_metadata_entry(
        &bundle.contracts,
        trust_wp_obligation,
        &native_trust_ir_bundle,
        request,
        proof_obligation_id,
    )
    .expect("trust-wp proof context metadata should build")
    .expect("trust-wp proof context metadata should be emitted");
    let proof_context: serde_json::Value =
        serde_json::from_str(&entry.value).expect("proof context metadata should be JSON");
    let assumptions =
        proof_context["assumptions"].as_array().expect("proof context should preserve assumptions");
    let assertions =
        proof_context["assertions"].as_array().expect("proof context should preserve assertions");

    assert_eq!(assumptions.len(), 1);
    assert_eq!(assumptions[0]["index"].as_u64(), Some(0));
    assert_eq!(assumptions[0]["role"], "assumption");
    assert_eq!(assumptions[0]["claim"]["format"], "trust_wp_pure_expr_v1");
    assert_eq!(assumptions[0]["claim"]["payload"], "true");
    assert_eq!(
        assumptions[0]["native_obligation_id"].as_u64(),
        Some(proof_obligation_id.index() as u64)
    );
    assert_eq!(assertions.len(), 1);
    assert_eq!(assertions[0]["index"].as_u64(), Some(1));
    assert_eq!(assertions[0]["role"], "assertion");
    assert_eq!(assertions[0]["claim"]["format"], "trust_formula_v1");
}

#[test]
fn trust_wp_pure_expr_stable_text_refuses_machine_arithmetic_aliases() {
    let int = |value: i64| serde_json::json!({ "kind": "int", "value": value });
    let var = || serde_json::json!({ "kind": "var", "name": "x", "sort": "int" });

    for (op, canonical) in [("add", "add"), ("+", "add"), ("sub", "sub"), ("-", "sub")] {
        let arithmetic = serde_json::json!({
            "kind": "binary",
            "op": op,
            "lhs": var(),
            "rhs": int(1),
        });
        let predicate = serde_json::json!({
            "kind": "binary",
            "op": "gt",
            "lhs": arithmetic,
            "rhs": var(),
        });
        let error = trust_wp_pure_expr_stable_text(&predicate)
            .expect_err("machine arithmetic must never reach unbounded-Int stable text");
        assert!(error.contains(&format!("arithmetic operator `{canonical}`")), "{op}: {error}");
        assert!(error.contains("false at u64::MAX"), "{op}: {error}");
        assert!(error.contains("amendment 1"), "{op}: {error}");
    }
}

#[test]
fn trust_wp_pure_expr_stable_text_keeps_arithmetic_free_int_comparisons() {
    let predicate = serde_json::json!({
        "kind": "binary",
        "op": "and",
        "lhs": {
            "kind": "binary",
            "op": "ge",
            "lhs": { "kind": "var", "name": "x", "sort": "int" },
            "rhs": { "kind": "int", "value": -5 },
        },
        "rhs": {
            "kind": "binary",
            "op": "eq",
            "lhs": { "kind": "var", "name": "ready", "sort": "bool" },
            "rhs": { "kind": "bool", "value": true },
        },
    });

    assert_eq!(
        trust_wp_pure_expr_stable_text(&predicate),
        Ok(("((x >= -5) && (ready == true))".to_string(), TrustWpPureExprSort::Bool)),
        "negative integer literals and arithmetic-free comparisons remain in the exact fragment",
    );
}

#[test]
fn trust_wp_pure_expr_stable_text_keeps_bool_identity_canonical() {
    let var = |name: &str| serde_json::json!({"kind": "var", "name": name, "sort": "bool"});
    let cases = [
        (var("flag"), "flag"),
        (serde_json::json!({"kind": "not", "expr": var("flag")}), "(! flag)"),
        (
            serde_json::json!({
                "kind": "binary",
                "op": "and",
                "lhs": var("flag"),
                "rhs": var("ready"),
            }),
            "(flag && ready)",
        ),
        (
            serde_json::json!({
                "kind": "binary",
                "op": "eq",
                "lhs": var("flag"),
                "rhs": {"kind": "bool", "value": true},
            }),
            "(flag == true)",
        ),
        (
            serde_json::json!({
                "kind": "binary",
                "op": "eq",
                "lhs": var("flag"),
                "rhs": var("ready"),
            }),
            "((flag == true) == (ready == true))",
        ),
        (
            serde_json::json!({
                "kind": "binary",
                "op": "ne",
                "lhs": var("flag"),
                "rhs": var("ready"),
            }),
            "((flag == true) != (ready == true))",
        ),
        (
            serde_json::json!({
                "kind": "not",
                "expr": {
                    "kind": "binary",
                    "op": "eq",
                    "lhs": var("flag"),
                    "rhs": var("ready"),
                },
            }),
            "(! ((flag == true) == (ready == true)))",
        ),
    ];
    for (value, expected) in cases {
        assert_eq!(
            trust_wp_pure_expr_stable_text(&value),
            Ok((expected.to_string(), TrustWpPureExprSort::Bool)),
            "compiler metadata keeps canonical public/native identity; the adapter expands Bool vars only at the final sibling request"
        );
    }
}

#[test]
fn trust_wp_pure_expr_stable_text_rejects_bool_ordering_and_conflicting_variable_sorts() {
    let bool_var = || serde_json::json!({"kind": "var", "name": "x", "sort": "bool"});
    let int_var = || serde_json::json!({"kind": "var", "name": "x", "sort": "int"});

    let bool_ordering = serde_json::json!({
        "kind": "binary",
        "op": "lt",
        "lhs": bool_var(),
        "rhs": bool_var(),
    });
    let error = trust_wp_pure_expr_stable_text(&bool_ordering)
        .expect_err("Bool ordering is outside the typed PureExpr grammar");
    assert!(error.contains("does not accept operand sorts"), "{error}");

    let mixed_sort = serde_json::json!({
        "kind": "binary",
        "op": "and",
        "lhs": bool_var(),
        "rhs": {
            "kind": "binary",
            "op": "ge",
            "lhs": int_var(),
            "rhs": {"kind": "int", "value": 0},
        },
    });
    let error = trust_wp_pure_expr_stable_text(&mixed_sort)
        .expect_err("one stable-text variable cannot carry Bool and Int sorts");
    assert!(error.contains("conflicting sorts"), "{error}");

    for alias in ["==", "!=", "<", "<=", ">", ">=", "&&", "||", "=>", "==>"] {
        let boolean = matches!(alias, "==" | "!=" | "&&" | "||" | "=>" | "==>");
        let value = serde_json::json!({
            "kind": "binary",
            "op": alias,
            "lhs": if boolean { bool_var() } else { int_var() },
            "rhs": if boolean { bool_var() } else { int_var() },
        });
        let error = trust_wp_pure_expr_stable_text(&value)
            .expect_err("typed JSON accepts canonical enum labels only");
        assert!(error.contains("binary op"), "{alias}: {error}");
    }
}

#[test]
fn trust_wp_replay_atom_claims_refuse_arithmetic_and_duplicate_envelopes() {
    for schema in [TRUST_WP_PURE_EXPR_SCHEMA_VERSION, "PureExpr"] {
        for payload in [
            "(x + 1) > x",
            "(x - 1) < x",
            "(x * 2) > x",
            "(x / 2) <= x",
            "(x % 2) == 0",
            "(x << 1) > x",
            "(x >> 1) <= x",
            "(x & 1) == 0",
            "(x | 1) >= x",
            "(x ^ 1) != x",
            "(~x) < 0",
            "-x < 0",
        ] {
            let formula = trust_ir::ProofFormula::new(schema, payload);
            let error = trust_wp_proof_claim_from_trust_ir_formula(&formula)
                .expect_err("legacy replay-atom arithmetic must fail at construction");
            assert!(error.contains("arithmetic operator"), "{schema}/{payload}: {error}");
        }
        for payload in [
            "x as u8 == x",
            "(x: u8) == x",
            "f(x) == f(x)",
            "x.field == x.field",
            "old(x) == old(x)",
            "x[0] == x[0]",
        ] {
            let formula = trust_ir::ProofFormula::new(schema, payload);
            let error = trust_wp_proof_claim_from_trust_ir_formula(&formula)
                .expect_err("reinterpretable replay-atom syntax must fail at construction");
            assert!(
                error.contains("arithmetic-free") || error.contains("stable text"),
                "{schema}/{payload}: {error}"
            );
        }
    }

    for op in ["add", "+", "sub", "-"] {
        let json = serde_json::json!({
            "kind": "binary",
            "op": "gt",
            "lhs": {
                "kind": "binary",
                "op": op,
                "lhs": {"kind": "var", "name": "x", "sort": "int"},
                "rhs": {"kind": "int", "value": 1},
            },
            "rhs": {"kind": "var", "name": "x", "sort": "int"},
        });
        let formula =
            trust_ir::ProofFormula::new(TRUST_WP_PURE_EXPR_SCHEMA_VERSION, json.to_string());
        let error = trust_wp_proof_claim_from_trust_ir_formula(&formula)
            .expect_err("JSON replay-atom arithmetic must fail at construction");
        assert!(error.contains("arithmetic operator"), "{op}: {error}");
    }

    let envelope = serde_json::json!({
        "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "gt",
            "lhs": {
                "op": "add",
                "lhs": {"var": "x"},
                "rhs": {"int": 1},
            },
            "rhs": {"var": "x"},
        },
    });
    let formula =
        trust_ir::ProofFormula::new(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION, envelope.to_string());
    assert!(trust_wp_proof_claim_from_trust_ir_formula(&formula).is_err());

    let duplicate = format!(
        r#"{{"schema":"{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}","body":{{"bool":true}},"body":{{"bool":false}}}}"#
    );
    let formula = trust_ir::ProofFormula::new(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION, duplicate);
    let error = trust_wp_proof_claim_from_trust_ir_formula(&formula)
        .expect_err("duplicate raw envelope keys must fail closed");
    assert!(error.contains("duplicate JSON object key `body`"), "{error}");

    let duplicate_nested_op = r#"{
        "kind":"binary",
        "op":"and",
        "lhs":{
            "kind":"binary",
            "op":"add",
            "op":"eq",
            "lhs":{"kind":"int","value":1},
            "rhs":{"kind":"int","value":1}
        },
        "rhs":{"kind":"bool","value":true}
    }"#;
    let formula =
        trust_ir::ProofFormula::new(TRUST_WP_PURE_EXPR_SCHEMA_VERSION, duplicate_nested_op);
    let error = trust_wp_proof_claim_from_trust_ir_formula(&formula)
        .expect_err("nested duplicate PureExpr operators must fail closed");
    assert!(error.contains("duplicate JSON object key `op`"), "{error}");

    let formula = trust_ir::ProofFormula::new(TRUST_WP_PURE_EXPR_SCHEMA_VERSION, "x >= -5");
    let claim = trust_wp_proof_claim_from_trust_ir_formula(&formula)
        .expect("negative literals remain arithmetic-free constants");
    assert_eq!(claim.payload, "x >= -5");
}

#[test]
fn trust_wp_legacy_pure_expr_contract_refuses_machine_arithmetic() {
    for payload in [
        "(x + 1) > x",
        "(x - 1) < x",
        "(x * 2) > x",
        "(x / 2) <= x",
        "(x % 2) == 0",
        "(x << 1) > x",
        "(x >> 1) <= x",
        "(x & 1) == 0",
        "(x | 1) >= x",
        "(x ^ 1) != x",
        "(~x) < 0",
    ] {
        let predicate = trust_verifier_api::ContractPredicate::CanonicalJson {
            schema: "PureExpr".to_string(),
            value: serde_json::Value::String(payload.to_string()),
        };
        let error = trust_wp_public_typed_proof_claim_from_contract_predicate(
            "contract-legacy-arithmetic",
            "obligation-legacy-arithmetic",
            &predicate,
        )
        .expect_err("legacy contract arithmetic must fail closed");
        assert!(error.contains("arithmetic operator"), "{payload}: {error}");
    }
}

#[test]
fn trust_wp_typed_value_ingresses_refuse_unknown_fields_and_formula_arithmetic() {
    let unknown_pure_expr = serde_json::json!({
        "kind": "not",
        "expr": {"kind": "bool", "value": false, "ignored": true},
    });
    let error = trust_wp_public_typed_proof_claim_from_schema_value(
        TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
        &unknown_pure_expr,
    )
    .expect_err("metadata PureExpr ingress must reject nested unknown fields");
    assert!(error.contains("unsupported field `ignored`"), "{error}");

    for invalid_name in ["true", "forall", "if", "x.field", "x#s1", "true) || true || (false"] {
        let ambiguous_var = serde_json::json!({
            "kind": "binary",
            "op": "eq",
            "lhs": {"kind": "var", "name": invalid_name, "sort": "bool"},
            "rhs": {"kind": "bool", "value": false},
        });
        let error = trust_wp_public_typed_proof_claim_from_schema_value(
            TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
            &ambiguous_var,
        )
        .expect_err("typed stable-text variables must be one opaque downstream token");
        assert!(error.contains("var name"), "{invalid_name}: {error}");
    }

    let opaque_var = serde_json::json!({
        "kind": "binary",
        "op": "ge",
        "lhs": {"kind": "var", "name": "_x_0_s1", "sort": "int"},
        "rhs": {"kind": "int", "value": -5},
    });
    let claim = trust_wp_public_typed_proof_claim_from_schema_value(
        TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
        &opaque_var,
    )
    .expect("opaque identifier value ingress succeeds")
    .expect("typed PureExpr produces a claim");
    assert_eq!(claim.payload, "(_x_0_s1 >= -5)");

    let unknown_contract = trust_verifier_api::ContractPredicate::CanonicalJson {
        schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
        value: unknown_pure_expr,
    };
    let error = trust_wp_public_typed_proof_claim_from_contract_predicate(
        "contract-unknown-pure-field",
        "obligation-unknown-pure-field",
        &unknown_contract,
    )
    .expect_err("contract PureExpr ingress must reject nested unknown fields");
    assert!(error.contains("unsupported field `ignored`"), "{error}");

    let arithmetic_envelope = serde_json::json!({
        "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        "variables": [{"name": "x", "sort": "int"}],
        "body": {
            "op": "gt",
            "lhs": {
                "op": "add",
                "lhs": {"var": "x"},
                "rhs": {"int": 1},
            },
            "rhs": {"var": "x"},
        },
    });
    let error = trust_wp_public_typed_proof_claim_from_schema_value(
        TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        &arithmetic_envelope,
    )
    .expect_err("metadata TrustFormula ingress must reject arithmetic");
    assert!(error.contains("arithmetic operator `add`"), "{error}");

    let arithmetic_contract = trust_verifier_api::ContractPredicate::CanonicalJson {
        schema: TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.to_string(),
        value: arithmetic_envelope,
    };
    let error = trust_wp_public_typed_proof_claim_from_contract_predicate(
        "contract-arithmetic-formula",
        "obligation-arithmetic-formula",
        &arithmetic_contract,
    )
    .expect_err("contract TrustFormula ingress must reject arithmetic");
    assert!(error.contains("arithmetic operator `add`"), "{error}");

    let x = || trust_types::Formula::Var("x".to_string(), trust_types::Sort::Int);
    let formula = trust_types::Formula::Gt(
        Box::new(trust_types::Formula::Add(Box::new(x()), Box::new(trust_types::Formula::Int(1)))),
        Box::new(x()),
    );
    let formula_value = serde_json::to_value(formula).expect("Formula@1 serializes");
    let formula_contract = trust_verifier_api::ContractPredicate::CanonicalJson {
        schema: TRUST_TYPES_FORMULA_SCHEMA_VERSION.to_string(),
        value: formula_value.clone(),
    };
    assert!(
        trust_wp_public_typed_proof_claim_from_contract_predicate(
            "contract-formula-at-1-arithmetic",
            "obligation-formula-at-1-arithmetic",
            &formula_contract,
        )
        .expect("unsupported Formula@1 lowering is represented without a construction error")
        .is_none(),
        "contract Formula@1 arithmetic must remain unsupported",
    );
    assert!(
        trust_wp_public_typed_proof_claim_from_schema_value(
            TRUST_TYPES_FORMULA_SCHEMA_VERSION,
            &formula_value,
        )
        .expect("unsupported Formula@1 metadata is represented without a construction error")
        .is_none(),
        "metadata Formula@1 arithmetic must remain unsupported",
    );
}

#[test]
fn trust_wp_metadata_raw_json_rejects_nested_duplicate_keys() {
    let duplicate_nested_op = r#"{
        "kind":"binary",
        "op":"and",
        "lhs":{
            "kind":"binary",
            "op":"add",
            "op":"eq",
            "lhs":{"kind":"int","value":1},
            "rhs":{"kind":"int","value":1}
        },
        "rhs":{"kind":"bool","value":true}
    }"#;
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "obligation-metadata-duplicate-pure-op".to_string(),
        kind: trust_verifier_api::ObligationKind::Postcondition,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "duplicate PureExpr metadata operator".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: duplicate_nested_op.to_string(),
            },
        ],
    };

    let error = trust_wp_public_typed_proof_claim_from_obligation_metadata(&obligation)
        .expect_err("raw metadata must reject nested duplicate proof JSON keys");
    assert!(error.contains("duplicate JSON object key `op`"), "{error}");
    let error = trust_wp_typed_contract_predicate_from_obligation_metadata(&obligation).expect_err(
        "compiler-derived typed contracts must reject nested duplicate proof JSON keys",
    );
    assert!(error.contains("duplicate JSON object key `op`"), "{error}");

    let mut duplicate_schema = obligation.clone();
    duplicate_schema.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
        value: TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.to_string(),
    });
    assert!(
        trust_wp_public_typed_proof_claim_from_obligation_metadata(&duplicate_schema)
            .expect("ambiguous schema metadata is safely ignored")
            .is_none(),
        "duplicate formula-schema metadata must not select either schema",
    );

    let mut duplicate_payload = obligation;
    duplicate_payload
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
        .expect("original payload metadata")
        .value = r#"{"kind":"bool","value":true}"#.to_string();
    duplicate_payload.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
        value: r#"{"kind":"bool","value":false}"#.to_string(),
    });
    let error = trust_wp_public_typed_proof_claim_from_obligation_metadata(&duplicate_payload)
        .expect_err("duplicate payload metadata must fail closed under a unique schema");
    assert!(
        error.contains(TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            && error.contains("no `trust.vc.formula.payload` payload"),
        "{error}"
    );
}

#[test]
fn full_verification_compiler_input_classifies_missing_native_bundle_and_direct_acceptance() {
    let (function, compiler_contracts, vcs) = native_trust_ir_compiler_function();
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    assert!(
        native_trust_ir_bundle.expect("native TrustIr bundle build should not fail").is_some(),
        "fixture obligations should require a typed native TrustIr bundle"
    );

    let calls = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let engine = trust_router::FullVerificationEngine::new(
        vec![
            Box::new(NativeTrustIrUnitEngine::new(
                "trust-wp",
                trust_verifier_api::EngineKind::Deductive,
                trust_verifier_api::ObligationKind::Postcondition,
                trust_verifier_api::ProofStrength::deductive(),
                vec![
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                        "trust-wp-solver-transcript",
                    ),
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::ProofCheckReport,
                        "trust-wp-proof-check",
                    ),
                ],
                calls.clone(),
            )),
            Box::new(NativeTrustIrUnitEngine::new(
                "trust-mc",
                trust_verifier_api::EngineKind::Reachability,
                trust_verifier_api::ObligationKind::ArithmeticSafety,
                trust_verifier_api::ProofStrength {
                    reasoning: trust_verifier_api::ReasoningKind::Pdr,
                    assurance: trust_verifier_api::AssuranceLevel::SmtBacked,
                },
                vec![
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                        "trust-mc-solver-transcript",
                    ),
                    native_trust_ir_test_artifact(
                        trust_verifier_api::EvidenceArtifactKind::ProofCheckReport,
                        "trust-mc-proof-check",
                    ),
                ],
                calls.clone(),
            )),
            Box::new(NativeTrustIrUnitEngine::new(
                "trust-vc",
                trust_verifier_api::EngineKind::Deductive,
                trust_verifier_api::ObligationKind::Ownership,
                trust_verifier_api::ProofStrength::certified(
                    trust_verifier_api::ReasoningKind::OwnershipAnalysis,
                ),
                vec![trust_vc_native_trust_ir_test_proof_certificate_artifact(
                    "trust-vc-proof-certificate",
                )],
                calls.clone(),
            )),
        ],
        trust_router::FullVerificationPolicy {
            require_all_required_engines: false,
            ..trust_router::FullVerificationPolicy::default()
        },
    );

    let result = verify_full_bundle_with_optional_native_trust_ir(
        &engine,
        &bundle,
        &bundle.obligations,
        None,
        &trust_router::VerifierExecutionContext::new("trustc-native-trust-ir-missing-test"),
    );

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 1);
    // The compiler-authored default TrustMC function row is the one exact
    // admission. Of the three real proof requests, trust-wp and trust-mc lack
    // their typed native bundle while the release-admissible structured
    // TrustVC row is proved independently by the direct lane.
    assert_eq!(result.summary.admitted, 1);
    assert_eq!(
        result.summary.missing_proof_artifacts, 2,
        "the two real native-bundle requests should fail closed without typed artifacts: {result:#?}"
    );
    assert_eq!(result.summary.unsupported, 0);
    assert!(
        result
            .evidence
            .iter()
            .filter(|evidence| {
                evidence.obligation_id != "vc:demo__checked_transfer:ownership:1"
            })
            .all(|evidence| {
                evidence.diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("no typed TrustIr NativeVerificationBundle was supplied")
                })
            }),
        "native-suite evidence must be rejected without the typed native TrustIr bundle: {result:#?}"
    );
    let direct = result
        .evidence
        .iter()
        .find(|evidence| evidence.obligation_id == "vc:demo__checked_transfer:ownership:1")
        .expect("direct TrustVC row should retain its own accepted evidence");
    assert_eq!(direct.status, trust_verifier_api::EvidenceStatus::Proved);
    assert_eq!(
        direct.proof_strength.as_ref(),
        Some(&trust_verifier_api::ProofStrength::certified(
            trust_verifier_api::ReasoningKind::OwnershipAnalysis,
        )),
    );
    assert!(direct.artifacts.iter().any(|artifact| {
        artifact.kind == trust_verifier_api::EvidenceArtifactKind::ProofCertificate
            && artifact.materialization.is_some()
    }));

    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured.len(), 4);
    let direct = structured
        .iter()
        .find(|item| item.obligation_id == "vc:demo__checked_transfer:ownership:1")
        .expect("structured direct TrustVC row");
    assert!(direct.has_accepted_proof());
    assert!(direct.blockers.is_empty());

    assert!(structured.iter().filter(|item| item.obligation_id != direct.obligation_id).all(
        |item| {
            !item.has_accepted_proof()
                && item.native_trust_ir.as_ref().is_some_and(|native| {
                    !native.has_matching_artifacts()
                        && (native.request_id.zip(native.proof_obligation_id).is_some()
                            || native.identity_error.as_ref().is_some_and(|error| {
                                error.contains("missing TrustIr native proof-obligation identity")
                            }))
                })
                && item.blockers.iter().any(|blocker| {
                    matches!(
                        blocker,
                        FullVerificationEvidenceBlocker::NativeTrustIrArtifactMismatch { .. }
                    )
                })
        }
    ));
}

#[test]
fn non_local_mir_scope_depends_on_policy() {
    let default_policy = test_policy(false, false);
    let full_self_build_policy = test_policy(false, false);
    let full_dependency_policy = test_policy(false, true);
    assert!(should_skip_non_local_mir_for_policy(false, &default_policy));
    assert!(should_skip_non_local_mir_for_policy(false, &full_self_build_policy));
    assert!(!should_skip_non_local_mir_for_policy(false, &full_dependency_policy));
    assert!(!should_skip_non_local_mir_for_policy(true, &default_policy));
}

#[test]
fn local_external_bucket_is_verified_without_a_corpus_allowlist() {
    let default_policy = test_policy(false, false);
    // Local (crate-under-compilation) bodies always verify. Non-local bodies
    // stay out of scope unless dependencies are explicitly included.
    assert!(!should_skip_external_dep_body(true, &default_policy));
    assert!(should_skip_external_dep_body(false, &default_policy));

    let bucket = trust_mir_extract::policy::PolicyBucket::ExternalDep;
    assert_eq!(
        verification_scope_policy_decision(bucket, true, &default_policy),
        TrustVerifyDecision::Verify
    );
    assert_eq!(
        verification_scope_policy_decision(bucket, false, &default_policy),
        TrustVerifyDecision::Skip(TrustVerifySkipReason::ExternalDependencyScope)
    );
}

#[test]
fn dependency_scope_verifies_external_dependencies_instead_of_skip_aborting() {
    let full_policy = test_policy(false, false);
    let full_dependency_policy = test_policy(false, true);

    // Local bodies always verify (never external-dependency scope); non-local
    // bodies verify only when dependency scope is explicitly included.
    assert!(!should_skip_external_dep_body(true, &full_policy));
    assert!(should_skip_external_dep_body(false, &full_policy));
    assert!(!should_skip_external_dep_body(true, &full_dependency_policy));
    assert!(!should_skip_external_dep_body(false, &full_dependency_policy));
}

#[test]
fn external_dependency_body_scope_routes_to_verifier_by_policy() {
    let normal_policy = test_policy(false, false);
    let dependency_policy = TrustVerifyPolicy { include_dependencies: true, ..normal_policy };
    let full_policy = test_policy(false, false);
    let full_dependency_policy = test_policy(false, true);

    let bucket = trust_mir_extract::policy::PolicyBucket::ExternalDep;

    assert_eq!(
        verification_scope_policy_decision(bucket, false, &normal_policy),
        TrustVerifyDecision::Skip(TrustVerifySkipReason::ExternalDependencyScope)
    );
    assert_eq!(
        verification_scope_policy_decision(bucket, false, &dependency_policy),
        TrustVerifyDecision::Verify
    );
    assert_eq!(
        verification_scope_policy_decision(bucket, false, &full_policy),
        TrustVerifyDecision::Skip(TrustVerifySkipReason::ExternalDependencyScope)
    );
    assert_eq!(
        verification_scope_policy_decision(bucket, false, &full_dependency_policy),
        TrustVerifyDecision::Verify
    );

    let trust_owned_bucket = trust_mir_extract::policy::PolicyBucket::TrustOwnedDefault;
    assert_eq!(
        verification_scope_policy_decision(trust_owned_bucket, false, &normal_policy),
        TrustVerifyDecision::Skip(TrustVerifySkipReason::NonLocalMir)
    );
    assert_eq!(
        verification_scope_policy_decision(trust_owned_bucket, false, &full_policy),
        TrustVerifyDecision::Skip(TrustVerifySkipReason::NonLocalMir)
    );
    assert_eq!(
        verification_scope_policy_decision(trust_owned_bucket, false, &full_dependency_policy),
        TrustVerifyDecision::Verify
    );
}

#[test]
fn full_verification_accepts_only_verified_summary() {
    let summary = TrustFunctionSummary {
        total: 2,
        trusted: 1,
        certified: 1,
        cached: 0,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        max_level: TrustProofLevel::None,
    };

    assert_eq!(full_verification_failure(&summary, &[], &[], &[], &[]), None);
}

#[test]
fn full_verification_flags_failed_unknown_runtime_and_unaccounted_artifacts() {
    let summary = TrustFunctionSummary {
        total: 5,
        trusted: 1,
        certified: 0,
        cached: 0,
        failed: 1,
        unknown: 1,
        runtime_checked: 1,
        max_level: TrustProofLevel::None,
    };

    assert_eq!(
        full_verification_failure(&summary, &[], &[], &[], &[]),
        Some(FullVerificationFailure { failed: 1, unknown: 1, runtime_checked: 1, skipped: 1 }),
    );
}

#[test]
fn strict_scope_treats_every_non_proved_bucket_as_fatal() {
    for failure in [
        FullVerificationFailure { failed: 1, unknown: 0, runtime_checked: 0, skipped: 0 },
        FullVerificationFailure { failed: 0, unknown: 1, runtime_checked: 0, skipped: 0 },
        FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 1, skipped: 0 },
        FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 },
    ] {
        assert!(
            strict_failure_is_fatal(failure),
            "strict scope must reject every unproved outcome bucket: {failure:?}"
        );
    }
    assert!(!strict_failure_is_fatal(FullVerificationFailure {
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        skipped: 0,
    }));
}

#[test]
fn full_verification_flags_skipped_transport_artifacts() {
    let summary = TrustFunctionSummary {
        total: 1,
        trusted: 1,
        certified: 0,
        cached: 0,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        max_level: TrustProofLevel::None,
    };
    let transport_result = TransportObligationResult {
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "divzero".to_string(),
        typed_kind: None,
        description: "division by zero".to_string(),
        location: None,
        outcome: Outcome::Skipped,
        solver: "mock".to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some("backend skipped obligation".to_string()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
    };

    assert_eq!(
        full_verification_failure(&summary, &[transport_result], &[], &[], &[]),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

#[test]
fn full_verification_flags_zero_obligation_summary() {
    let summary = TrustFunctionSummary {
        total: 0,
        trusted: 0,
        certified: 0,
        cached: 0,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        max_level: TrustProofLevel::None,
    };

    assert_eq!(
        full_verification_failure(&summary, &[], &[], &[], &[]),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

fn native_run_result(
    status: trust_verifier_api::VerificationRunStatus,
    summary: trust_verifier_api::VerificationRunSummary,
) -> trust_verifier_api::VerificationRunResult {
    let engine = trust_verifier_api::EngineManifest::new(
        "test-engine",
        "0.0.0",
        trust_verifier_api::EngineKind::Composite,
    );
    let requested_obligations = (0..summary.requested_obligations)
        .map(|idx| trust_verifier_api::TrustObligation {
            obligation_id: format!("obligation-{idx}"),
            kind: trust_verifier_api::ObligationKind::ArithmeticSafety,
            contract_id: None,
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation::default(),
            description: format!("test obligation {idx}"),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        })
        .collect::<Vec<_>>();
    let evidence = (0..summary.proved)
        .map(|idx| trust_verifier_api::ObligationEvidence {
            evidence_id: format!("evidence-{idx}"),
            obligation_id: format!("obligation-{idx}"),
            engine: engine.clone(),
            status: trust_verifier_api::EvidenceStatus::Proved,
            proof_strength: Some(trust_verifier_api::ProofStrength::smt_unsat()),
            artifacts: vec![trust_verifier_api::EvidenceArtifact {
                kind: trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                uri: format!("artifact://test/solver-transcript-{idx}.smt2"),
                hash: trust_verifier_api::ArtifactHash {
                    algorithm: "sha256".to_string(),
                    value: format!("{idx:064x}"),
                },
                materialization: None,
            }],
            counterexample: None,
            publication: trust_verifier_api::EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        })
        .collect::<Vec<_>>();

    trust_verifier_api::VerificationRunResult {
        schema_version: trust_verifier_api::RUN_MANIFEST_SCHEMA_VERSION.to_string(),
        run_id: "test-run".to_string(),
        bundle_id: "test-bundle".to_string(),
        subject: trust_verifier_api::BundleSubject::Function {
            crate_name: "test".to_string(),
            path: "test::f".to_string(),
        },
        engine,
        context: trust_verifier_api::VerifierExecutionSnapshot::default(),
        status,
        summary,
        requested_obligations,
        evidence,
        skipped: vec![],
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: vec![],
    }
}

fn native_temporal_proved_run() -> trust_verifier_api::VerificationRunResult {
    let mut run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Proved,
        trust_verifier_api::VerificationRunSummary {
            requested_obligations: 1,
            evidence_count: 1,
            proved: 1,
            ..trust_verifier_api::VerificationRunSummary::default()
        },
    );
    run.requested_obligations[0].kind = trust_verifier_api::ObligationKind::TemporalSafety;
    run.evidence[0].proof_strength = Some(trust_verifier_api::ProofStrength::certified(
        trust_verifier_api::ReasoningKind::TemporalModelCheck,
    ));
    run.evidence[0].artifacts =
        exact_native_unit_test_proof_dag(&run.evidence[0].obligation_id, "ty", "temporal-proof");
    authority_test_rebuild_run(&run, run.requested_obligations.clone(), run.evidence.clone())
}

fn native_test_default_admission() -> trust_verifier_api::TrustObligation {
    let (mut function, _, _) = native_trust_ir_compiler_function();
    function.contracts.clear();
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-native-accounting-admission",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: function.def_path.clone(),
        },
    );
    build_native_trust_ir_bundle_for_test_verifier_api(&function, &mut bundle, &[])
        .expect("native TrustIr bundle builds")
        .expect("default admission creates a native request");
    bundle
        .obligations
        .into_iter()
        .find(trust_verifier_api::TrustObligation::is_default_admission)
        .expect("compiler emits one exact default admission")
}

#[test]
fn native_full_verification_empty_is_a_proof_gap() {
    let run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Empty,
        trust_verifier_api::VerificationRunSummary::default(),
    );

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

#[test]
fn native_full_verification_rejects_trust_ir_route_with_only_solver_transcript() {
    let run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Proved,
        trust_verifier_api::VerificationRunSummary {
            requested_obligations: 1,
            evidence_count: 1,
            proved: 1,
            ..trust_verifier_api::VerificationRunSummary::default()
        },
    );

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

#[test]
fn native_full_verification_ty_proved_is_accepted_without_trust_ir_artifacts() {
    let run = native_temporal_proved_run();

    assert_eq!(native_full_verification_failure(Some(&run)), None);
}

#[test]
fn native_full_verification_ignores_only_one_exact_default_admission() {
    let run = native_temporal_proved_run();
    let admission = native_test_default_admission();
    let requested = vec![run.requested_obligations[0].clone(), admission.clone()];
    let with_admission = authority_test_rebuild_run(&run, requested, run.evidence.clone());
    assert_eq!(with_admission.summary.requested_obligations, 1);
    assert_eq!(with_admission.summary.admitted, 1);
    assert_eq!(native_full_verification_failure(Some(&with_admission)), None);

    let duplicate = authority_test_rebuild_run(
        &run,
        vec![run.requested_obligations[0].clone(), admission.clone(), admission.clone()],
        run.evidence.clone(),
    );
    assert!(
        native_full_verification_failure(Some(&duplicate)).is_some(),
        "duplicate admission IDs must invalidate strict exact coverage"
    );

    let mut second_admission = admission.clone();
    second_admission.obligation_id = "vc:second_function:trust_mc_default_function:0".to_string();
    assert!(second_admission.is_default_admission());
    let multiple = authority_test_rebuild_run(
        &run,
        vec![run.requested_obligations[0].clone(), admission.clone(), second_admission],
        run.evidence.clone(),
    );
    assert!(
        native_full_verification_failure(Some(&multiple)).is_some(),
        "a function may carry at most one exact synthetic admission"
    );

    let mut malformed = admission;
    malformed.metadata.push(trust_verifier_api::MetadataEntry {
        key: trust_verifier_api::TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY.to_string(),
        value: trust_verifier_api::TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE.to_string(),
    });
    assert!(!malformed.is_default_admission());
    let malformed = authority_test_rebuild_run(
        &run,
        vec![run.requested_obligations[0].clone(), malformed],
        run.evidence.clone(),
    );
    assert!(
        native_full_verification_failure(Some(&malformed)).is_some(),
        "a marker lookalike is a real unproved row, never an excluded admission"
    );
}

#[test]
fn native_full_verification_rejects_proved_run_without_artifacts() {
    let mut run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Proved,
        trust_verifier_api::VerificationRunSummary {
            requested_obligations: 1,
            evidence_count: 1,
            proved: 1,
            ..trust_verifier_api::VerificationRunSummary::default()
        },
    );
    run.evidence[0].artifacts.clear();

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

#[test]
fn native_full_verification_rejects_zero_obligation_proved_run() {
    let run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Proved,
        trust_verifier_api::VerificationRunSummary::default(),
    );

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

#[test]
fn native_full_verification_rejects_unaccounted_proved_run() {
    let run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Proved,
        trust_verifier_api::VerificationRunSummary {
            requested_obligations: 2,
            evidence_count: 1,
            proved: 1,
            ..trust_verifier_api::VerificationRunSummary::default()
        },
    );

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 2 }),
    );
}

#[test]
fn native_full_verification_rejects_missing_evidence_rows_for_proved_run() {
    let mut run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Proved,
        trust_verifier_api::VerificationRunSummary {
            requested_obligations: 1,
            evidence_count: 1,
            proved: 1,
            ..trust_verifier_api::VerificationRunSummary::default()
        },
    );
    run.evidence.clear();

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
    );
}

#[test]
fn native_full_verification_preserves_failed_unknown_and_skipped_counts() {
    let run = native_run_result(
        trust_verifier_api::VerificationRunStatus::Inconclusive,
        trust_verifier_api::VerificationRunSummary {
            requested_obligations: 6,
            failed: 1,
            unknown: 1,
            timed_out: 1,
            unsupported: 1,
            skipped: 1,
            missing_proof_artifacts: 1,
            ..trust_verifier_api::VerificationRunSummary::default()
        },
    );

    assert_eq!(
        native_full_verification_failure(Some(&run)),
        Some(FullVerificationFailure { failed: 1, unknown: 2, runtime_checked: 0, skipped: 3 }),
    );
}

fn authority_test_native_obligation(
    obligation_id: &str,
    proof_id: u32,
    line: u32,
) -> trust_verifier_api::TrustObligation {
    trust_verifier_api::TrustObligation {
        obligation_id: obligation_id.to_string(),
        kind: trust_verifier_api::ObligationKind::ArithmeticSafety,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation {
            file: Some("authority.rs".to_string()),
            line: Some(line),
            column: Some(1),
            end_line: Some(line),
            end_column: Some(5),
            ..trust_verifier_api::SourceLocation::default()
        },
        description: "authority-bound arithmetic safety".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                    .to_string(),
                value: "trust-mc".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                    .to_string(),
                value: "7".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
                    .to_string(),
                value: proof_id.to_string(),
            },
        ],
    }
}

fn authority_test_native_artifact_lineage(
    suite: &str,
    request_id: &str,
    proof_id: &str,
) -> Vec<trust_verifier_api::EvidenceArtifact> {
    use trust_verifier_api::{
        ArtifactHash, EvidenceArtifact, EvidenceArtifactKind, EvidenceArtifactMaterialization,
        EvidenceArtifactReference,
    };

    fn canonicalize(value: &mut serde_json::Value) {
        match value {
            serde_json::Value::Array(values) => {
                for value in values {
                    canonicalize(value);
                }
            }
            serde_json::Value::Object(object) => {
                let old = std::mem::take(object);
                let mut entries = old.into_iter().collect::<Vec<_>>();
                entries.sort_by(|left, right| left.0.cmp(&right.0));
                for (key, mut value) in entries {
                    canonicalize(&mut value);
                    object.insert(key, value);
                }
            }
            _ => {}
        }
    }

    fn materialize(
        role: &str,
        suite: Option<&str>,
        request_id: Option<&str>,
        proof_id: Option<&str>,
        binding: &str,
        references: Vec<EvidenceArtifactReference>,
    ) -> (EvidenceArtifactMaterialization, ArtifactHash) {
        let mut value = serde_json::json!({
            "schema": trust_types::NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
            "role": role,
            "suite": suite,
            "request_id": request_id,
            "proof_id": proof_id,
            "payload": { "authority_test": role },
        });
        canonicalize(&mut value);
        let bytes = serde_json::to_vec(&value).expect("serialize native authority fixture");
        let hash = ArtifactHash {
            algorithm: "sha256".to_string(),
            value: trust_types::stable_sha256_hex(&bytes),
        };
        let materialization =
            EvidenceArtifactMaterialization::new(bytes, binding.to_string(), references)
                .expect("materialize native authority fixture");
        (materialization, hash)
    }

    let binding = native_trust_ir_proof_unit_id(
        suite,
        request_id.parse().expect("numeric request id"),
        proof_id.parse().expect("numeric proof id"),
    );
    let (bundle_materialization, bundle_hash) =
        materialize("bundle", None, None, None, &binding, Vec::new());
    let bundle = EvidenceArtifact {
        kind: EvidenceArtifactKind::EngineInput,
        uri: format!("trust_ir-native://verification-bundle/{}", bundle_hash.value),
        hash: bundle_hash,
        materialization: Some(bundle_materialization),
    };
    let (request_materialization, request_hash) = materialize(
        "request",
        Some(suite),
        Some(request_id),
        None,
        &binding,
        vec![EvidenceArtifactReference { kind: bundle.kind, hash: bundle.hash.clone() }],
    );
    let request = EvidenceArtifact {
        kind: EvidenceArtifactKind::EngineInput,
        uri: format!("{}/{suite}/request/{request_id}/{}", bundle.uri, request_hash.value),
        hash: request_hash,
        materialization: Some(request_materialization),
    };
    let (proof_materialization, proof_hash) = materialize(
        "normalized_obligation",
        Some(suite),
        Some(request_id),
        Some(proof_id),
        &binding,
        vec![EvidenceArtifactReference { kind: request.kind, hash: request.hash.clone() }],
    );
    let proof = EvidenceArtifact {
        kind: EvidenceArtifactKind::NormalizedObligation,
        uri: format!("{}/proof/{proof_id}/{}", request.uri, proof_hash.value),
        hash: proof_hash,
        materialization: Some(proof_materialization),
    };
    vec![bundle, request, proof]
}

fn authority_test_strict_native_run(
    obligation: trust_verifier_api::TrustObligation,
) -> trust_verifier_api::VerificationRunResult {
    let identity = native_transport_identity(&obligation);
    let request_id = identity.request_id.as_deref().expect("request id");
    let proof_id = identity.proof_id.as_deref().expect("proof id");
    let mut artifacts =
        exact_native_unit_test_proof_dag(&obligation.obligation_id, "trust-mc", "authority-token");
    artifacts.extend(authority_test_native_artifact_lineage("trust-mc", request_id, proof_id));
    let evidence = trust_verifier_api::ObligationEvidence {
        evidence_id: format!("authority:{}", obligation.obligation_id),
        obligation_id: obligation.obligation_id.clone(),
        engine: trust_verifier_api::EngineManifest::new(
            "trust-mc",
            "authority-test",
            trust_verifier_api::EngineKind::Reachability,
        ),
        status: trust_verifier_api::EvidenceStatus::Proved,
        proof_strength: Some(trust_verifier_api::ProofStrength::smt_unsat()),
        artifacts,
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: vec!["typed TrustIr native request identity accepted".to_string()],
    };
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "authority-bundle",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "authority".to_string(),
            path: "authority::f".to_string(),
        },
    );
    bundle.obligations.push(obligation.clone());
    trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("authority-test").snapshot(),
        &bundle,
        evidence.engine.clone(),
        &[obligation],
        vec![evidence],
    )
}

fn authority_test_direct_trust_vc_obligation(
    obligation_id: &str,
    line: u32,
) -> trust_verifier_api::TrustObligation {
    trust_verifier_api::TrustObligation {
        obligation_id: obligation_id.to_string(),
        kind: trust_verifier_api::ObligationKind::MemorySafety,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation {
            file: Some("authority-direct.rs".to_string()),
            line: Some(line),
            column: Some(1),
            end_line: Some(line),
            end_column: Some(5),
            ..trust_verifier_api::SourceLocation::default()
        },
        description: "authority-bound direct TrustVC memory safety".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY
                    .to_string(),
                value: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED
                    .to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY
                    .to_string(),
                value: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON.to_string(),
            },
        ],
    }
}

fn authority_test_direct_trust_vc_run(
    obligation: trust_verifier_api::TrustObligation,
) -> trust_verifier_api::VerificationRunResult {
    use trust_verifier_api::{
        EvidenceArtifact, EvidenceArtifactKind, EvidenceArtifactMaterialization,
    };

    let binding = format!("trust-vc-direct-mir-memory:{}", obligation.obligation_id);
    let artifact = |kind, uri_prefix: &str, bytes: &[u8]| {
        let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
            kind,
            bytes,
            &binding,
            &obligation.obligation_id,
            Vec::new(),
        )
        .expect("direct authority artifact materializes");
        EvidenceArtifact {
            kind,
            uri: format!("{uri_prefix}{}", hash.value),
            hash,
            materialization: Some(materialization),
        }
    };
    let mut normalized = artifact(
        EvidenceArtifactKind::NormalizedObligation,
        "artifact://trust-vc/direct-authority/normalized/",
        b"direct authority normalized obligation",
    );
    let mut input = artifact(
        EvidenceArtifactKind::EngineInput,
        "artifact://trust-vc/direct-authority/input/",
        b"direct authority engine input",
    );
    // The genuine direct lane publishes these as supplemental audit hashes,
    // not as separately materialized proof nodes. Only the unique Alethe
    // certificate owns the proof binding under the certificate artifact route.
    normalized.materialization = None;
    input.materialization = None;
    let mut certificate = artifact(
        EvidenceArtifactKind::ProofCertificate,
        trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX,
        b"direct authority checked alethe certificate",
    );
    certificate.uri.push_str(".alethe");
    let mut engine = trust_verifier_api::EngineManifest::new(
        "trust-full-verifier",
        trust_verifier_api::API_VERSION,
        trust_verifier_api::EngineKind::Composite,
    );
    engine.proof_modes.push(trust_verifier_api::ReasoningKind::OwnershipAnalysis);
    let evidence = trust_verifier_api::ObligationEvidence {
        evidence_id: format!("trust-vc:direct-mir-memory:test:{}", obligation.obligation_id),
        obligation_id: obligation.obligation_id.clone(),
        engine: engine.clone(),
        status: trust_verifier_api::EvidenceStatus::Proved,
        proof_strength: Some(trust_verifier_api::ProofStrength::certified(
            trust_verifier_api::ReasoningKind::OwnershipAnalysis,
        )),
        artifacts: vec![normalized, input, certificate],
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: vec!["primary owner trust-vc produced accepted direct evidence".to_string()],
    };
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "authority-direct-bundle",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "authority".to_string(),
            path: "authority::direct".to_string(),
        },
    );
    bundle.obligations.push(obligation.clone());
    trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("authority-direct-test").snapshot(),
        &bundle,
        engine,
        &[obligation],
        vec![evidence],
    )
}

fn authority_test_rebuild_run(
    run: &trust_verifier_api::VerificationRunResult,
    requested_obligations: Vec<trust_verifier_api::TrustObligation>,
    evidence: Vec<trust_verifier_api::ObligationEvidence>,
) -> trust_verifier_api::VerificationRunResult {
    let mut bundle =
        trust_verifier_api::TrustContractBundle::empty(run.bundle_id.clone(), run.subject.clone());
    bundle.obligations = requested_obligations.clone();
    trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("authority-test-rebuild").snapshot(),
        &bundle,
        run.engine.clone(),
        &requested_obligations,
        evidence,
    )
}

fn authority_test_proved() -> VerificationResult {
    VerificationResult::Proved {
        solver: trust_types::Symbol::intern("forged-public-label"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat_strict_checked(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

#[test]
fn exact_source_clause_discharge_preserves_public_private_carrier_parity() {
    let span = native_trust_ir_test_span(70);
    let contracts = vec![
        trust_types::Contract {
            kind: trust_types::ContractKind::Ensures,
            span: span.clone(),
            body: "true".to_string(),
        },
        trust_types::Contract {
            kind: trust_types::ContractKind::Ensures,
            span: native_trust_ir_test_span(71),
            body: "false".to_string(),
        },
    ];
    let function = trust_types::VerifiableFunction {
        name: "two_clauses".to_string(),
        def_path: "demo::two_clauses".to_string(),
        span: span.clone(),
        body: trust_types::VerifiableBody {
            locals: vec![trust_types::LocalDecl {
                index: 0,
                ty: trust_types::Ty::Bool,
                name: Some("_0".to_string()),
            }],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 0,
            return_ty: trust_types::Ty::Bool,
        },
        contracts: contracts.clone(),
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: trust_types::Symbol::intern("demo::two_clauses"),
        location: native_trust_ir_test_span(72),
        // Keep the body row symbolic so its strict/kernel proof can pass the
        // ordinary anti-vacuity gate. The authored catalog marker below still
        // exercises the non-semantic `Bool(false)` placeholder.
        formula: trust_types::Formula::Var("body_violation".to_string(), Sort::Bool),
        contract_metadata: Some(trust_types::ContractMetadata {
            has_ensures: true,
            source_contract_index: Some(0),
            ..trust_types::ContractMetadata::default()
        }),
    };
    let compiler_contracts = trust_types::CompilerContractBundle::new(contracts);
    let (bundle, _) = build_full_verification_input_for_tests(
        &function,
        &compiler_contracts,
        std::slice::from_ref(&vc),
    );
    let body = bundle
        .obligations
        .iter()
        .find(|obligation| {
            exactly_one_metadata_value(
                &obligation.metadata,
                TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY,
            ) == Some("0")
        })
        .expect("clause-A body VC")
        .clone();
    let mut markers: Vec<_> = bundle
        .obligations
        .iter()
        .filter_map(|obligation| {
            source_clause_marker_identity(&bundle, obligation)
                .map(|identity| (identity.index, obligation.clone()))
        })
        .collect();
    markers.sort_by_key(|(index, _)| *index);
    assert_eq!(markers.len(), 2);

    let strict = authority_test_strict_native_run(body.clone());
    let body_evidence = strict.evidence.into_iter().next().expect("strict body evidence");
    let run_engine = body_evidence.engine.clone();
    let mut evidence = vec![
        body_evidence,
        unsupported_evidence_for(&markers[0].1),
        unsupported_evidence_for(&markers[1].1),
    ];
    for row in &mut evidence {
        row.engine = run_engine.clone();
    }
    let run = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("exact-clause-test").snapshot(),
        &bundle,
        run_engine,
        &bundle.obligations,
        evidence,
    );
    let rekey_snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        std::slice::from_ref(&vc),
        run.context.clone(),
    );
    assert!(source_clause_body_link(&bundle, &body, &vc).is_some(), "body link must validate");
    assert!(
        strict_full_verification_accepted_obligation_ids(&run).contains(&body.obligation_id),
        "body evidence must enter the private strict index: {:#?}",
        run.to_manifest()
    );
    assert!(
        exact_source_clause_marker_ids(&bundle, &run, std::slice::from_ref(&vc), &rekey_snapshot,)
            .contains(&markers[0].1.obligation_id),
        "clause A marker must be eligible"
    );
    let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &run,
        std::slice::from_ref(&vc),
        &rekey_snapshot,
    );
    let by_id: FxHashMap<_, _> = bundle
        .obligations
        .iter()
        .filter(|obligation| !obligation.is_default_admission())
        .zip(results.iter())
        .map(|(obligation, (_, result))| (obligation.obligation_id.as_str(), result))
        .collect();
    assert!(matches!(
        by_id[markers[0].1.obligation_id.as_str()],
        VerificationResult::Unknown { solver, .. }
            if solver.as_str() == "trust-exact-source-clause-discharge"
    ));
    assert!(matches!(
        by_id[markers[1].1.obligation_id.as_str()],
        VerificationResult::Unknown { .. }
    ));

    let result_obligation_ids = bundle
        .obligations
        .iter()
        .filter(|obligation| !obligation.is_default_admission())
        .map(|obligation| obligation.obligation_id.as_str())
        .collect::<Vec<_>>();
    let marker_a_index = result_obligation_ids
        .iter()
        .position(|id| *id == markers[0].1.obligation_id)
        .expect("clause A marker result index");
    let marker_b_index = result_obligation_ids
        .iter()
        .position(|id| *id == markers[1].1.obligation_id)
        .expect("clause B marker result index");
    let body_index = result_obligation_ids
        .iter()
        .position(|id| *id == body.obligation_id)
        .expect("clause A body result index");
    assert!(
        matches!(results[marker_a_index].0.formula, Formula::Bool(false)),
        "fixture must exercise the catalog-marker vacuity representation"
    );

    let mut generically_promoted = results.clone();
    generically_promoted[marker_a_index].1 = authority_test_proved();
    assert_eq!(
        keep_exact_source_clause_markers_pending(&bundle, &mut generically_promoted, &bindings),
        2,
        "both recognized catalog markers must be normalized before certification"
    );
    assert!(matches!(
        &generically_promoted[marker_a_index].1,
        VerificationResult::Unknown { solver, .. }
            if solver.as_str() == "trust-exact-source-clause-discharge"
    ));

    // Public strict evidence is deliberately insufficient by itself: phase one
    // leaves both source markers Unknown and no empty authority carrier may
    // change either catalog row.
    let mut public_only_results = results.clone();
    let public_only_bindings = bindings.clone();
    let mut public_only_authorities = vec![None; results.len()];
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut public_only_results,
            &public_only_bindings,
            &mut public_only_authorities,
        ),
        0,
        "accepted public body evidence must not directly discharge a source marker"
    );
    assert!(matches!(&public_only_results[marker_a_index].1, VerificationResult::Unknown { .. }));

    // Accepted public evidence remains attribution-only. The generic builder
    // must not mint even a row-aligned native token from serializable state.
    let cleancic = vec![None; results.len()];
    let mut legacy_authorities =
        build_result_proof_authorities(&results, &bindings, Some(&run), &cleancic);
    assert!(legacy_authorities.iter().all(Option::is_none));
    let mut legacy_results = results.clone();
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut legacy_results,
            &bindings,
            &mut legacy_authorities,
        ),
        0,
        "public native evidence without a private capability must not discharge a marker"
    );
    assert!(matches!(&legacy_results[marker_a_index].1, VerificationResult::Unknown { .. }));

    // A Clean kernel certificate is the only qualifying body capability.
    // Solver revalidation and native replay remain excluded rather than being
    // inferred from membership in some other static authority lane.
    let mut kernel_cleancic = vec![None; results.len()];
    kernel_cleancic[body_index] = Some(authority_test_clean_cic(91));
    let mut authorities =
        build_result_proof_authorities(&results, &bindings, Some(&run), &kernel_cleancic);
    assert!(matches!(
        authorities[body_index].as_ref(),
        Some(ResultProofAuthority::KernelCertified { .. })
    ));
    assert!(authorities[marker_a_index].is_none());
    assert!(authorities[marker_b_index].is_none());

    let mut swapped_results = results.clone();
    let swapped_bindings = bindings.clone();
    let mut swapped_authorities = authorities.clone();
    swapped_authorities.swap(body_index, marker_a_index);
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut swapped_results,
            &swapped_bindings,
            &mut swapped_authorities,
        ),
        0,
        "moving an otherwise-valid private token away from its exact body row must fail closed"
    );

    let body_binding = bindings[body_index].clone().expect("exact body binding");
    let body_row =
        exact_result_row_identity(body_index, &results[body_index].0).expect("exact body row");
    let mut recursive_results = results.clone();
    let mut recursive_authorities = authorities.clone();
    recursive_authorities[body_index] = Some(ResultProofAuthority::ExactSourceClauseDischarge {
        row: body_row.clone(),
        binding: body_binding,
        body_proofs: vec![ExactSourceClauseBodyProofBinding {
            public_obligation_id: body.obligation_id.clone(),
            row: body_row,
        }],
    });
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut recursive_results,
            &bindings,
            &mut recursive_authorities,
        ),
        0,
        "a source-derived token must never recursively authorize a source body"
    );

    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut results,
            &bindings,
            &mut authorities,
        ),
        1,
        "one sealed KernelCertified body authority must discharge exactly clause A"
    );
    let source_authority = authorities[marker_a_index]
        .as_ref()
        .expect("exact body authority must mint source-clause authority");
    assert!(matches!(
        source_authority,
        ResultProofAuthority::ExactSourceClauseDischarge { body_proofs, .. }
            if body_proofs.len() == 1
                && body_proofs[0].public_obligation_id == body.obligation_id
                && body_proofs[0].row
                    == exact_result_row_identity(body_index, &results[body_index].0)
                        .expect("exact body row")
    ));
    assert!(source_authority.is_static_proof_for(
        marker_a_index,
        &results[marker_a_index].0,
        &results[marker_a_index].1,
        bindings[marker_a_index].as_ref(),
    ));
    let mut empty_source_authority = source_authority.clone();
    let ResultProofAuthority::ExactSourceClauseDischarge { body_proofs, .. } =
        &mut empty_source_authority
    else {
        unreachable!()
    };
    body_proofs.clear();
    assert!(
        !empty_source_authority.matches_row(
            marker_a_index,
            &results[marker_a_index].0,
            bindings[marker_a_index].as_ref(),
        ),
        "an empty body-proof provenance carrier must not retain source-clause authority",
    );

    // A concrete marker refutation remains a blocker even when the complete
    // body group has an otherwise-valid kernel capability.
    let mut failed_evidence = run.evidence.clone();
    let failed_marker = failed_evidence
        .iter_mut()
        .find(|evidence| evidence.obligation_id == markers[0].1.obligation_id)
        .expect("clause A marker evidence");
    failed_marker.status = trust_verifier_api::EvidenceStatus::Failed;
    failed_marker.proof_strength = None;
    failed_marker.artifacts.clear();
    failed_marker.counterexample = None;
    failed_marker.diagnostics = vec!["concrete source-marker refutation".to_string()];
    let failed_run = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("exact-clause-failed-marker-test").snapshot(),
        &bundle,
        run.engine.clone(),
        &bundle.obligations,
        failed_evidence,
    );
    let failed_rekey_snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        std::slice::from_ref(&vc),
        failed_run.context.clone(),
    );
    let (mut failed_results, failed_bindings) =
        full_verification_legacy_results_bound_with_fresh_vcs(
            &function,
            &bundle,
            &failed_run,
            std::slice::from_ref(&vc),
            &failed_rekey_snapshot,
        );
    assert!(
        matches!(&failed_results[marker_a_index].1, VerificationResult::Failed { .. }),
        "concrete marker refutation must remain Failed, got {:?}",
        failed_results[marker_a_index].1,
    );
    let mut failed_authorities = build_result_proof_authorities(
        &failed_results,
        &failed_bindings,
        Some(&failed_run),
        &kernel_cleancic,
    );
    assert!(matches!(
        failed_authorities[body_index].as_ref(),
        Some(ResultProofAuthority::KernelCertified { .. })
    ));
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &failed_run,
            std::slice::from_ref(&vc),
            &failed_rekey_snapshot,
            &mut failed_results,
            &failed_bindings,
            &mut failed_authorities,
        ),
        0,
        "a concrete marker refutation must block derived discharge"
    );
    assert!(matches!(&failed_results[marker_a_index].1, VerificationResult::Failed { .. }));

    // Revocation is authority-driven too. Removing the exact body capability
    // must clear the derived marker even though the public run is unchanged.
    let mut revoked_results = results.clone();
    let revoked_bindings = bindings.clone();
    let mut revoked_authorities = authorities.clone();
    revoked_authorities[body_index] = None;
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut revoked_results,
            &revoked_bindings,
            &mut revoked_authorities,
        ),
        0,
        "losing the sealed body authority must revoke the derived capability"
    );
    assert!(matches!(&revoked_results[marker_a_index].1, VerificationResult::Unknown { .. }));
    assert!(revoked_authorities[marker_a_index].is_none());

    let mut stale_results = results.clone();
    let mut stale_authorities = authorities.clone();
    stale_authorities.swap(marker_a_index, marker_b_index);
    stale_authorities[body_index] = None;
    assert!(matches!(&stale_results[marker_a_index].1, VerificationResult::Proved { .. }));
    assert_eq!(
        apply_exact_source_clause_discharges(
            &bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
            &mut stale_results,
            &bindings,
            &mut stale_authorities,
        ),
        0,
        "a stale Proved marker with its source authority swapped away must be normalized"
    );
    assert!(matches!(&stale_results[marker_a_index].1, VerificationResult::Unknown { .. }));
    assert!(stale_authorities.iter().all(|authority| !matches!(
        authority,
        Some(ResultProofAuthority::ExactSourceClauseDischarge { .. })
    )));

    let proof_results = build_proof_results_with_runtime_checks(
        false,
        &results,
        &[],
        &bindings,
        &authorities,
        Some(&function),
    );
    let marker_a_disposition =
        proof_results.dispositions.iter().nth(marker_a_index).expect("clause A proof disposition");
    let marker_b_disposition =
        proof_results.dispositions.iter().nth(marker_b_index).expect("clause B proof disposition");
    assert_eq!(marker_a_disposition.status, TrustStatus::Trusted);
    assert_eq!(marker_a_disposition.strength, TrustProofStrength::Deductive);
    assert_eq!(marker_b_disposition.status, TrustStatus::Unknown);

    let transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &results,
        Some(&run),
        &kernel_cleancic,
        &bindings,
        &authorities,
    );
    assert_eq!(transport[marker_a_index].outcome, Outcome::Proved);
    assert_eq!(transport[marker_a_index].solver, "trust-exact-source-clause-discharge");
    assert_eq!(transport[marker_b_index].outcome, Outcome::Unknown);

    assert!(run.evidence.iter().any(|evidence| {
        evidence.obligation_id == markers[0].1.obligation_id
            && evidence.status == trust_verifier_api::EvidenceStatus::Unsupported
    }));
    assert!(run.evidence.iter().any(|evidence| {
        evidence.obligation_id == markers[1].1.obligation_id
            && evidence.status == trust_verifier_api::EvidenceStatus::Unsupported
    }));
    assert_eq!(run.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    run.validate_derived_state().expect("public source-marker run stays canonical");
    run.try_to_manifest().expect("public source-marker run stays manifestable");

    let mut tampered = body.clone();
    tampered
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
        .expect("predicate digest")
        .value = "0".repeat(64);
    assert!(source_clause_body_link(&bundle, &tampered, &vc).is_none());
    let mut duplicate = body.clone();
    duplicate.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY.to_string(),
        value: "0".to_string(),
    });
    assert!(source_clause_body_link(&bundle, &duplicate, &vc).is_none());

    for (key, value) in [
        (TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY, "1"),
        (TRUST_VC_SOURCE_CONTRACT_ROLE_METADATA_KEY, "loop_decreases"),
        (TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY, "tampered-digest"),
    ] {
        let mut tampered_bundle = bundle.clone();
        tampered_bundle
            .obligations
            .iter_mut()
            .find(|obligation| obligation.obligation_id == body.obligation_id)
            .expect("body row")
            .metadata
            .iter_mut()
            .find(|entry| entry.key == key)
            .expect("source-link metadata")
            .value = value.to_string();
        let (tampered_results, tampered_bindings) =
            full_verification_legacy_results_bound_with_fresh_vcs(
                &function,
                &tampered_bundle,
                &run,
                std::slice::from_ref(&vc),
                &rekey_snapshot,
            );
        assert!(
            tampered_results
                .iter()
                .all(|(_, result)| { matches!(result, VerificationResult::Unknown { .. }) })
        );
        assert!(tampered_results.iter().any(|(row, _)| {
            matches!(
                &row.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "fresh-vc-rekey-integrity"
            )
        }));
        assert!(tampered_bindings.iter().all(Option::is_none));
    }

    let mut repointed_bundle = bundle.clone();
    repointed_bundle
        .obligations
        .iter_mut()
        .find(|obligation| obligation.obligation_id == body.obligation_id)
        .expect("body row")
        .contract_id = Some("trust-contract:demo::two_clauses:clause:1".to_string());
    let (repointed_results, repointed_bindings) =
        full_verification_legacy_results_bound_with_fresh_vcs(
            &function,
            &repointed_bundle,
            &run,
            std::slice::from_ref(&vc),
            &rekey_snapshot,
        );
    assert!(
        repointed_results
            .iter()
            .all(|(_, result)| { matches!(result, VerificationResult::Unknown { .. }) })
    );
    assert!(repointed_bindings.iter().all(Option::is_none));
}

#[test]
fn exact_source_clause_cardinality_is_kind_specific() {
    let identity = |kind| SourceClauseIdentity {
        index: 0,
        contract_id: "trust-contract:demo::f:clause:0".to_string(),
        predicate_digest: "a".repeat(64),
        kind,
    };
    assert!(source_clause_body_group_is_complete(
        &identity(SourceClauseKind::LoopInvariant),
        &[
            (0, SourceClauseRole::LoopInvariantInitiation),
            (1, SourceClauseRole::LoopInvariantConsecution),
        ],
    ));
    assert!(!source_clause_body_group_is_complete(
        &identity(SourceClauseKind::LoopInvariant),
        &[(0, SourceClauseRole::LoopInvariantInitiation)],
    ));
    assert!(source_clause_body_group_is_complete(
        &identity(SourceClauseKind::Decreases),
        &[(0, SourceClauseRole::LoopDecreases)],
    ));
    assert!(!source_clause_body_group_is_complete(
        &identity(SourceClauseKind::Decreases),
        &[(0, SourceClauseRole::LoopDecreases), (1, SourceClauseRole::LoopDecreases),],
    ));
    assert!(!source_clause_body_group_is_complete(
        &identity(SourceClauseKind::Decreases),
        &[(0, SourceClauseRole::RecursionDecreases)],
    ));
    assert!(!source_clause_body_group_is_complete(
        &identity(SourceClauseKind::Decreases),
        &[(0, SourceClauseRole::RecursionDecreases), (1, SourceClauseRole::RecursionDecreases),],
    ));
    assert!(source_clause_body_group_is_complete(
        &identity(SourceClauseKind::Ensures),
        &[(0, SourceClauseRole::Postcondition), (1, SourceClauseRole::Postcondition),],
    ));
    assert!(!source_clause_body_group_is_complete(&identity(SourceClauseKind::Ensures), &[],));
}

#[test]
fn exact_source_clause_accepts_normal_contract_origin_e4_and_e5_markers() {
    for (label, contract_kind, obligation_kind, expected_kind) in [
        (
            "loop_invariant",
            trust_verifier_api::ContractKind::LoopInvariant,
            trust_verifier_api::ObligationKind::LoopInvariant,
            SourceClauseKind::LoopInvariant,
        ),
        (
            "decreases",
            trust_verifier_api::ContractKind::Asserts,
            trust_verifier_api::ObligationKind::Termination,
            SourceClauseKind::Decreases,
        ),
    ] {
        let contract_id = format!("trust-contract:demo::f:{label}:0");
        let predicate_digest = "a".repeat(64);
        let contract = trust_verifier_api::TrustContract {
            contract_id: contract_id.clone(),
            kind: contract_kind,
            predicate: trust_verifier_api::ContractPredicate::TrustExpr {
                text: "true".to_string(),
            },
            source: trust_verifier_api::SourceLocation::default(),
            metadata: vec![trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest.clone(),
            }],
        };
        let context = trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::Contract {
                contract_id: contract_id.clone(),
                contract_kind,
                contract_index: 0,
                predicate_schema: None,
            },
        );
        let marker = trust_verifier_api::TrustObligation {
            obligation_id: format!("trust-obligation:demo::f:{label}:0"),
            kind: obligation_kind,
            contract_id: Some(contract_id.clone()),
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation::default(),
            description: format!("normal {label} source marker"),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: vec![
                context.to_metadata_entry().expect("serialize marker origin"),
                trust_verifier_api::MetadataEntry {
                    key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                    value: predicate_digest.clone(),
                },
            ],
        };
        let mut bundle = trust_verifier_api::TrustContractBundle::empty(
            format!("normal-{label}-bundle"),
            trust_verifier_api::BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::f".to_string(),
            },
        );
        bundle.contracts.push(contract);
        bundle.obligations.push(marker.clone());

        assert_eq!(
            source_clause_marker_identity(&bundle, &marker),
            Some(SourceClauseIdentity {
                index: 0,
                contract_id,
                predicate_digest,
                kind: expected_kind,
            }),
            "normal Contract-origin {label} marker must retain exact source identity"
        );
    }
}

fn authority_test_clean_cic(seed: u8) -> trust_ir::ProofEvidence {
    trust_ir::ProofEvidence::CleanCic {
        term: vec![seed],
        context: vec![seed.wrapping_add(1)],
        lineage: trust_ir::ProofDigest::sha256_domain("authority-test", &[seed]),
        kernel_recheck: None,
    }
}

fn proof_feedback_source_span(line: u32) -> trust_types::SourceSpan {
    trust_types::SourceSpan {
        file: "feedback.rs".to_string(),
        line_start: line,
        col_start: 4,
        line_end: line,
        col_end: 20,
    }
}

fn proof_feedback_loop_function() -> trust_types::VerifiableFunction {
    let clause_span = proof_feedback_source_span(8);
    trust_types::VerifiableFunction {
        name: "feedback_loop".to_string(),
        def_path: "test::feedback_loop".to_string(),
        span: proof_feedback_source_span(1),
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Unit,
                    name: Some("_0".into()),
                },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::u32(),
                    name: Some("n".into()),
                },
                trust_types::LocalDecl {
                    index: 2,
                    ty: trust_types::Ty::u32(),
                    name: Some("i".into()),
                },
                trust_types::LocalDecl {
                    index: 3,
                    ty: trust_types::Ty::Bool,
                    name: Some("cond".into()),
                },
            ],
            blocks: vec![
                trust_types::BasicBlock {
                    id: trust_types::BlockId(0),
                    stmts: vec![
                        trust_types::Statement::Assign {
                            place: trust_types::Place::local(1),
                            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                                trust_types::ConstValue::Int(10),
                            )),
                            span: proof_feedback_source_span(2),
                        },
                        trust_types::Statement::Assign {
                            place: trust_types::Place::local(2),
                            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(
                                trust_types::Place::local(1),
                            )),
                            span: proof_feedback_source_span(3),
                        },
                    ],
                    terminator: trust_types::Terminator::Goto(trust_types::BlockId(1)),
                },
                trust_types::BasicBlock {
                    id: trust_types::BlockId(1),
                    stmts: vec![trust_types::Statement::Assign {
                        place: trust_types::Place::local(3),
                        rvalue: trust_types::Rvalue::BinaryOp(
                            trust_types::BinOp::Gt,
                            trust_types::Operand::Copy(trust_types::Place::local(2)),
                            trust_types::Operand::Constant(trust_types::ConstValue::Int(0)),
                        ),
                        span: proof_feedback_source_span(4),
                    }],
                    terminator: trust_types::Terminator::SwitchInt {
                        discr: trust_types::Operand::Copy(trust_types::Place::local(3)),
                        targets: vec![(1, trust_types::BlockId(2))],
                        otherwise: trust_types::BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: proof_feedback_source_span(4),
                    },
                },
                trust_types::BasicBlock {
                    id: trust_types::BlockId(2),
                    stmts: vec![trust_types::Statement::Assign {
                        place: trust_types::Place::local(2),
                        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(
                            trust_types::Place::local(1),
                        )),
                        span: proof_feedback_source_span(5),
                    }],
                    terminator: trust_types::Terminator::Goto(trust_types::BlockId(1)),
                },
                trust_types::BasicBlock {
                    id: trust_types::BlockId(3),
                    stmts: Vec::new(),
                    terminator: trust_types::Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: trust_types::Ty::Unit,
        },
        contracts: vec![
            trust_types::Contract {
                kind: trust_types::ContractKind::LoopInvariant,
                span: clause_span.clone(),
                body: "bb1: n <= 10 && i <= 10".to_string(),
            },
            trust_types::Contract {
                kind: trust_types::ContractKind::Decreases,
                span: clause_span,
                body: "bb1: i".to_string(),
            },
        ],
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

fn proof_feedback_e4_indices(
    results: &[(VerificationCondition, VerificationResult)],
) -> (usize, usize) {
    let initiation = results
        .iter()
        .position(|(vc, _)| matches!(vc.kind, VcKind::LoopInvariantInitiation { .. }))
        .expect("E4 initiation row");
    let consecution = results
        .iter()
        .position(|(vc, _)| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .expect("E4 consecution row");
    (initiation, consecution)
}

fn proof_feedback_kernel_authorities(
    results: &[(VerificationCondition, VerificationResult)],
) -> Vec<Option<ResultProofAuthority>> {
    let mut authorities = vec![None; results.len()];
    let (initiation, consecution) = proof_feedback_e4_indices(results);
    for (seed, index) in [initiation, consecution].into_iter().enumerate() {
        authorities[index] = Some(ResultProofAuthority::KernelCertified {
            row: exact_result_row_identity(index, &results[index].0).expect("exact E4 row"),
            evidence: authority_test_clean_cic(seed as u8),
        });
    }
    authorities
}

/// Both E4 rows carrying S1 solver-replay authority: a genuine, exactly
/// row-bound static proof that is still not a kernel proof. It is the closest
/// non-kernel authority to the one the feedback gate accepts, which is what
/// pins the gate to kernel/S3 evidence rather than to "some private token is
/// present on the row".
fn proof_feedback_solver_revalidated_authorities(
    results: &[(VerificationCondition, VerificationResult)],
) -> Vec<Option<ResultProofAuthority>> {
    let mut authorities = vec![None; results.len()];
    let (initiation, consecution) = proof_feedback_e4_indices(results);
    for index in [initiation, consecution] {
        let vc = &results[index].0;
        let row = exact_result_row_identity(index, vc).expect("exact E4 row");
        let canonical_problem = trust_router::in_process_ay_backend::problem_smt2(&vc.formula);
        let authority = ResultProofAuthority::SolverRevalidated {
            row: row.clone(),
            receipt: SolverRevalidationReceipt {
                row_index: index,
                canonical_vc: row.canonical_vc,
                problem_sha256: trust_types::stable_sha256_hex(canonical_problem.as_bytes()),
                canonical_problem,
                time_ms: 1,
            },
        };
        assert!(
            authority.is_static_proof_for(index, vc, &results[index].1, None),
            "the fixture's S1 token must be a valid static proof of its own row",
        );
        authorities[index] = Some(authority);
    }
    authorities
}

fn proof_feedback_production_results(
    function: &trust_types::VerifiableFunction,
) -> Vec<(VerificationCondition, VerificationResult)> {
    let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(function);
    solver_vcs
        .into_iter()
        .chain(discharged.into_iter().map(|(vc, _)| vc))
        .map(|vc| (vc, authority_test_proved()))
        .collect()
}

#[test]
fn loop_feedback_requires_both_exact_private_e4_authorities_and_rejects_ambiguity() {
    let function = proof_feedback_loop_function();
    let mut results = proof_feedback_production_results(&function);
    let authorities = proof_feedback_kernel_authorities(&results);

    assert_eq!(
        proof_gated_loop_invariant_feedback_tokens(&function, &results, &[], &authorities)
            .expect("exact E4 rows should bind")
            .len(),
        1
    );

    let solver_authorities = proof_feedback_solver_revalidated_authorities(&results);
    assert!(
        proof_gated_loop_invariant_feedback_tokens(&function, &results, &[], &solver_authorities)
            .expect("trusted solver-replay authority is a clean non-match")
            .is_empty(),
        "Trusted, exactly row-bound S1 E4 rows must not strengthen a separate E5 obligation",
    );

    let (initiation, consecution) = proof_feedback_e4_indices(&results);
    assert!(
        trust_vcgen::loop_invariant_feedback_candidate(
            &function,
            &results[initiation].0,
            &results[consecution].0,
        )
        .is_some(),
        "the fixture has a valid structural candidate; only compiler-private authority is missing",
    );
    let public_labels_only = vec![None; results.len()];
    assert!(
        proof_gated_loop_invariant_feedback_tokens(&function, &results, &[], &public_labels_only,)
            .expect("missing authority is a clean non-match")
            .is_empty(),
        "public Proved labels must not mint feedback"
    );
    let mut one_leg = authorities.clone();
    one_leg[consecution] = None;
    assert!(
        proof_gated_loop_invariant_feedback_tokens(&function, &results, &[], &one_leg)
            .expect("one authorized leg is a clean non-match")
            .is_empty(),
        "one exact E4 proof must never license the invariant"
    );

    let mut stale_outcome = results.clone();
    stale_outcome[consecution].1 = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("stale-outcome-test"),
        time_ms: 0,
        reason: "the result changed after authority construction".to_string(),
    };
    assert!(
        proof_gated_loop_invariant_feedback_tokens(&function, &stale_outcome, &[], &authorities,)
            .expect("stale outcome is a clean non-match")
            .is_empty(),
        "an exact but stale authority must not license a row whose current outcome is not Proved"
    );

    results.push(results[initiation].clone());
    let mut ambiguous_authorities = authorities;
    ambiguous_authorities.push(None);
    assert!(
        proof_gated_loop_invariant_feedback_tokens(
            &function,
            &results,
            &[],
            &ambiguous_authorities,
        )
        .expect_err("duplicate E4 routing must fail closed")
        .contains("ambiguous E4 rows")
    );
}

#[test]
fn loop_feedback_replaces_only_complete_e5_routes_and_solves_every_changed_formula() {
    let function = proof_feedback_loop_function();
    let mut results = proof_feedback_production_results(&function);
    results.push((test_vc(999), authority_test_proved()));
    let authorities = proof_feedback_kernel_authorities(&results);
    let feedback =
        proof_gated_loop_invariant_feedback_tokens(&function, &results, &[], &authorities)
            .expect("exact E4 pair should bind");

    let current_vcs = results.iter().map(|(vc, _)| vc.clone()).collect::<Vec<_>>();
    let plan = proof_gated_loop_e5_replacement_plan(&function, &current_vcs, &feedback)
        .expect("complete E5 routes should pair exactly");
    assert!(!plan.is_empty());
    assert!(plan.iter().all(|replacement| replacement.changed));

    let wrapped_index =
        current_vcs.iter().position(is_loop_local_e5_row).expect("loop-local E5 row");
    let trust_types::Formula::And(current_wrapped_parts) = &current_vcs[wrapped_index].formula
    else {
        panic!("production E5 fixture should carry an interval environment")
    };
    let production_environment = current_wrapped_parts[0].clone();
    let production_baseline_formula = current_wrapped_parts[1].clone();
    let (raw_baseline, augmented_baseline) =
        trust_vcgen::regenerate_loop_decreases_with_invariant_feedback_production_variants(
            &function,
            &[],
        )
        .expect("baseline E5 production variants");
    let (raw_replacement, augmented_replacement) =
        trust_vcgen::regenerate_loop_decreases_with_invariant_feedback_production_variants(
            &function,
            &loop_feedback_candidates(&feedback),
        )
        .expect("replacement E5 production variants");
    let wrapped_route = exact_vc_routing_payload(&current_vcs[wrapped_index]).expect("E5 route");
    let variant_index = raw_baseline
        .iter()
        .position(|vc| exact_vc_routing_payload(vc).ok().as_ref() == Some(&wrapped_route))
        .expect("regenerated baseline route");
    assert_eq!(
        exact_vc_payload(&current_vcs[wrapped_index]),
        exact_vc_payload(&augmented_baseline[variant_index]),
        "the fixture must be the exact production augmentation, not just shape-compatible",
    );
    let wrapped_replacement = plan
        .iter()
        .find(|replacement| replacement.row_index == wrapped_index)
        .expect("wrapped E5 replacement");
    let trust_types::Formula::And(_) = &wrapped_replacement.replacement.formula else {
        panic!("replacement should retain the interval wrapper")
    };
    assert_eq!(
        exact_vc_payload(&wrapped_replacement.replacement),
        exact_vc_payload(&augmented_replacement[variant_index]),
        "an augmented input must select the exact recomputed augmented replacement",
    );

    let mut raw_current_vcs = current_vcs.clone();
    raw_current_vcs[wrapped_index].formula = raw_baseline[variant_index].formula.clone();
    let raw_plan = proof_gated_loop_e5_replacement_plan(&function, &raw_current_vcs, &feedback)
        .expect("an exact raw production row remains accepted");
    let raw_planned_replacement = raw_plan
        .iter()
        .find(|replacement| replacement.row_index == wrapped_index)
        .expect("raw E5 replacement");
    assert_eq!(
        exact_vc_payload(&raw_planned_replacement.replacement),
        exact_vc_payload(&raw_replacement[variant_index]),
        "a raw input must select the exact raw replacement",
    );

    for forged_environment in [
        trust_types::Formula::Bool(false),
        trust_types::Formula::Eq(
            Box::new(trust_types::Formula::Int(1)),
            Box::new(trust_types::Formula::Int(1)),
        ),
    ] {
        let mut forged_wrapper_vcs = current_vcs.clone();
        forged_wrapper_vcs[wrapped_index].formula = trust_types::Formula::And(vec![
            forged_environment,
            production_baseline_formula.clone(),
        ]);
        assert!(
            proof_gated_loop_e5_replacement_plan(&function, &forged_wrapper_vcs, &feedback)
                .expect_err("a forged shape-compatible environment must fail closed")
                .contains("exact production-augmented"),
        );
    }

    let mut unknown_wrapper_vcs = current_vcs.clone();
    unknown_wrapper_vcs[wrapped_index].formula = trust_types::Formula::And(vec![
        production_environment,
        trust_types::Formula::Bool(true),
        production_baseline_formula,
    ]);
    assert!(
        proof_gated_loop_e5_replacement_plan(&function, &unknown_wrapper_vcs, &feedback)
            .expect_err("an unknown E5 wrapper must fail closed")
            .contains("exact production-augmented")
    );

    let mut candidate = results.clone();
    for replacement in &plan {
        candidate[replacement.row_index].0 = replacement.replacement.clone();
    }
    assert_eq!(candidate.len(), results.len(), "E5 feedback replaces, never appends");
    let replaced = plan.iter().map(|row| row.row_index).collect::<std::collections::BTreeSet<_>>();
    for (index, row) in candidate.iter().enumerate() {
        if !replaced.contains(&index) {
            assert_eq!(
                serde_json::to_string(row).expect("candidate row serializes"),
                serde_json::to_string(&results[index]).expect("original row serializes"),
                "non-E5 row {index} changed"
            );
        }
    }
    for replacement in &plan {
        assert_eq!(
            exact_vc_payload(&candidate[replacement.row_index].0),
            exact_vc_payload(&replacement.replacement)
        );
    }

    let candidate_authorities = proof_feedback_kernel_authorities(&candidate);
    validate_proof_gated_loop_feedback_candidate(
        &function,
        &candidate,
        &[],
        &candidate_authorities,
        &feedback,
    )
    .expect("fresh exact E4 authority and complete E5 replacement should revalidate");

    let mut stale_e4 = candidate.clone();
    let (initiation, _) = proof_feedback_e4_indices(&stale_e4);
    stale_e4[initiation].0.formula = trust_types::Formula::Bool(false);
    assert!(
        validate_proof_gated_loop_feedback_candidate(
            &function,
            &stale_e4,
            &[],
            &candidate_authorities,
            &feedback,
        )
        .expect_err("formula drift must invalidate old row authority")
        .contains("E4 proof authority changed")
    );

    let mut ambiguous_vcs = current_vcs;
    ambiguous_vcs.push(
        trust_vcgen::regenerate_loop_decreases_with_invariant_feedback_vcs(&function, &[])
            .into_iter()
            .next()
            .expect("baseline E5 row"),
    );
    assert!(
        proof_gated_loop_e5_replacement_plan(&function, &ambiguous_vcs, &feedback)
            .expect_err("duplicate current E5 route must fail closed")
            .contains("cardinality")
    );

    let mut extra_route_vcs = results.iter().map(|(vc, _)| vc.clone()).collect::<Vec<_>>();
    let mut extra_e5 =
        trust_vcgen::regenerate_loop_decreases_with_invariant_feedback_vcs(&function, &[])
            .into_iter()
            .next()
            .expect("baseline E5 row");
    let VcKind::NonTermination { measure, .. } = &mut extra_e5.kind else {
        panic!("fixture E5 should be a termination row")
    };
    *measure = "different-measure".to_string();
    extra_e5.location.line_start += 100;
    extra_e5.location.line_end += 100;
    extra_route_vcs.push(extra_e5);
    assert!(
        proof_gated_loop_e5_replacement_plan(&function, &extra_route_vcs, &feedback)
            .expect_err("an extra loop-local E5 route must fail closed")
            .contains("cardinality")
    );
}

#[test]
fn full_input_threads_e4_capability_into_strengthened_e5_marker_replacement() {
    let function = proof_feedback_loop_function();
    let compiler_contracts = trust_types::CompilerContractBundle::new(function.contracts.clone());
    let results = proof_feedback_production_results(&function);
    let authorities = proof_feedback_kernel_authorities(&results);
    let feedback =
        proof_gated_loop_invariant_feedback_tokens(&function, &results, &[], &authorities)
            .expect("exact E4 proofs should mint one private capability");
    let mut refined_vcs = results.iter().map(|(vc, _)| vc.clone()).collect::<Vec<_>>();
    let plan = proof_gated_loop_e5_replacement_plan(&function, &refined_vcs, &feedback)
        .expect("the E4 capability should strengthen the exact E5 carrier");
    for replacement in plan {
        if replacement.changed {
            refined_vcs[replacement.row_index] = replacement.replacement;
        }
    }

    let (without_feedback, _) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &refined_vcs);
    assert!(
        without_feedback.obligations.iter().any(|obligation| {
            source_clause_marker_identity(&without_feedback, obligation)
                .is_some_and(|identity| identity.kind == SourceClauseKind::Decreases)
        }),
        "a strengthened E5 row must not look fresh to the capability-free first-pass API"
    );

    let (with_feedback, _) = build_full_verification_input_for_tests_with_loop_feedback(
        &function,
        &compiler_contracts,
        &refined_vcs,
        &feedback,
    );
    assert!(
        with_feedback.obligations.iter().all(|obligation| {
            source_clause_marker_identity(&with_feedback, obligation).is_none_or(|identity| {
                !matches!(
                    identity.kind,
                    SourceClauseKind::LoopInvariant | SourceClauseKind::Decreases
                )
            })
        }),
        "the compiler-minted capability must replace both E4 and strengthened E5 markers"
    );
}

#[test]
fn fresh_exact_direct_receipts_are_rebuilt_for_e5_pass_two() {
    let mut function = proof_feedback_loop_function();
    // The structural feedback fixture intentionally uses a non-decreasing loop
    // because its older tests inject solver labels. This integration battery
    // needs a genuinely provable E5 row, so make the guarded body decrement the
    // exact `i` measure while preserving the same E4/E5 routing structure.
    function.body.blocks[2].stmts[0] = trust_types::Statement::Assign {
        place: trust_types::Place::local(2),
        rvalue: trust_types::Rvalue::BinaryOp(
            trust_types::BinOp::Sub,
            trust_types::Operand::Copy(trust_types::Place::local(2)),
            trust_types::Operand::Constant(trust_types::ConstValue::Int(1)),
        ),
        span: proof_feedback_source_span(5),
    };
    let compiler_contracts = trust_types::CompilerContractBundle::new(function.contracts.clone());
    let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&function);
    let mut first_vcs = solver_vcs;
    first_vcs.extend(discharged.into_iter().map(|(vc, _)| vc));

    let mut first = fresh_exact_direct_fixture_for(
        &function,
        &compiler_contracts,
        &first_vcs,
        &[],
        "compiler-s3-e5-pass-one",
    );
    assert!(
        !first.live_receipts.fresh_exact_direct_chc_pdr_receipts().is_empty(),
        "pass one must return affine native receipts"
    );
    let mut first_authorities = vec![None; first.results.len()];
    let first_report = install_fresh_exact_direct_chc_pdr_authorities(
        &first.bundle,
        &first.dispatched,
        &first.context,
        &first.final_run,
        Some(&mut first.live_receipts),
        &first.results,
        &first.bindings,
        &mut first_authorities,
    );
    assert!(first_report.minted >= 2, "{:#?}", first_report.rejected);
    let (first_initiation, first_consecution) = proof_feedback_e4_indices(&first.results);
    let first_e4_links = [first_initiation, first_consecution].map(|index| {
        let binding = first.bindings[index].as_ref().expect("exact E4 result binding");
        source_clause_body_link(
            &first.bundle,
            &binding.canonical_obligation,
            &first.results[index].0,
        )
        .expect("exact E4 body link")
    });
    assert_eq!(first_e4_links[0].0, first_e4_links[1].0);
    assert_eq!(first_e4_links[0].0.kind, SourceClauseKind::LoopInvariant);
    assert!(matches!(
        (first_e4_links[0].1, first_e4_links[1].1),
        (SourceClauseRole::LoopInvariantInitiation, SourceClauseRole::LoopInvariantConsecution)
            | (
                SourceClauseRole::LoopInvariantConsecution,
                SourceClauseRole::LoopInvariantInitiation
            )
    ));
    assert!(
        first.bundle.obligations.iter().all(|obligation| {
            source_clause_marker_identity(&first.bundle, obligation)
                .is_none_or(|identity| identity.kind != SourceClauseKind::LoopInvariant)
        }),
        "an exact complete E4 pair must replace, rather than retain, the standalone source marker"
    );
    let first_run_seals = [first_initiation, first_consecution].map(|index| {
        let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
            first_authorities[index].as_ref()
        else {
            panic!("pass-one E4 row {index} must use a consumed fresh receipt")
        };
        assert_eq!(authority.run_seal.context.run_id, "compiler-s3-e5-pass-one");
        Arc::clone(&authority.run_seal)
    });
    let feedback = proof_gated_loop_invariant_feedback_tokens(
        &function,
        &first.results,
        &first.bindings,
        &first_authorities,
    )
    .expect("fresh exact-direct E4 receipts must enter the gated feedback lane");
    assert_eq!(feedback.len(), 1);

    let plan = proof_gated_loop_e5_replacement_plan(&function, &first_vcs, &feedback)
        .expect("fresh receipt-authorized E4 pair must produce an exact E5 plan");
    assert!(plan.iter().any(|replacement| replacement.changed));
    let mut refined_vcs = first_vcs;
    for replacement in plan.into_iter().filter(|replacement| replacement.changed) {
        refined_vcs[replacement.row_index] = replacement.replacement;
    }

    let mut second = fresh_exact_direct_fixture_for(
        &function,
        &compiler_contracts,
        &refined_vcs,
        &feedback,
        "compiler-s3-e5-pass-two",
    );
    assert!(
        !second.live_receipts.fresh_exact_direct_chc_pdr_receipts().is_empty(),
        "pass two must solve a fresh exact inventory"
    );
    let mut second_authorities = vec![None; second.results.len()];
    let second_report = install_fresh_exact_direct_chc_pdr_authorities(
        &second.bundle,
        &second.dispatched,
        &second.context,
        &second.final_run,
        Some(&mut second.live_receipts),
        &second.results,
        &second.bindings,
        &mut second_authorities,
    );
    assert!(second_report.minted >= 3, "{:#?}", second_report.rejected);
    let (second_initiation, second_consecution) = proof_feedback_e4_indices(&second.results);
    for index in [second_initiation, second_consecution] {
        let Some(ResultProofAuthority::FreshExactDirectChcPdr { authority }) =
            second_authorities[index].as_ref()
        else {
            panic!("pass-two E4 row {index} must be freshly receipt-authorized")
        };
        assert_eq!(authority.run_seal.context.run_id, "compiler-s3-e5-pass-two");
        assert!(
            first_run_seals
                .iter()
                .all(|first_run_seal| !Arc::ptr_eq(first_run_seal, &authority.run_seal)),
            "pass two must not reuse a pass-one affine run seal"
        );
    }
    assert!(
        second.results.iter().enumerate().any(|(index, (vc, result))| {
            matches!(vc.kind, VcKind::NonTermination { .. })
                && result.is_proved()
                && matches!(
                    second_authorities[index].as_ref(),
                    Some(ResultProofAuthority::FreshExactDirectChcPdr { .. })
                )
        }),
        "at least one regenerated E5 row must carry its pass-two affine receipt"
    );
    validate_proof_gated_loop_feedback_candidate(
        &function,
        &second.results,
        &second.bindings,
        &second_authorities,
        &feedback,
    )
    .expect("the fully rebuilt pass-two carrier must revalidate E4 and every changed E5 formula");
}

#[test]
fn strict_l0_verification_reports_raw_solver_proved_without_full_evidence() {
    let mut overflow = test_vc(10);
    overflow.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::i32(), trust_types::Ty::i32()),
    };
    let proved = VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    assert_eq!(
        strict_l0_verification_failure(true, &[(overflow.clone(), proved)], &[], &[], None),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 1, skipped: 0 }),
    );

    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        reason: "incomplete".to_string(),
    };
    assert_eq!(
        strict_l0_verification_failure(true, &[(overflow, unknown)], &[], &[], None),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 1, skipped: 0 }),
    );
}

#[test]
fn certified_monitor_transport_uses_original_bundle_metadata_and_exact_row_binding() {
    let mut monitored_obligation = authority_test_native_obligation("monitor:original:A", 51, 51);
    stamp_monitor_metadata(
        &mut monitored_obligation.metadata,
        "monitored",
        "Clean kernel accepted monitor equivalence",
        &format!("sha256:{}", "a".repeat(64)),
    );
    let mut unmonitored_obligation = authority_test_native_obligation("monitor:original:B", 52, 52);
    stamp_monitor_metadata(
        &mut unmonitored_obligation.metadata,
        "unmonitored",
        "quantified proposition has no finite monitor",
        &format!("sha256:{}", "b".repeat(64)),
    );

    let unknown = |label: &str| VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("monitor-transport-test"),
        time_ms: 0,
        reason: label.to_string(),
    };
    let results = vec![(test_vc(51), unknown("first")), (test_vc(52), unknown("second"))];
    let bindings = vec![
        result_obligation_binding(0, &results[0].0, &monitored_obligation),
        result_obligation_binding(1, &results[1].0, &unmonitored_obligation),
    ];
    let rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        None,
        &[None, None],
        &bindings,
        &[None, None],
    );
    assert_eq!(
        rows[0].monitor.as_ref().map(|monitor| monitor.status),
        Some(trust_types::TransportMonitorStatus::Monitored),
    );
    assert_eq!(
        rows[1].monitor.as_ref().map(|monitor| monitor.status),
        Some(trust_types::TransportMonitorStatus::Unmonitored),
    );

    // Even moving each binding with its original row cannot preserve the
    // capability after the result carrier is reordered: the private binding
    // owns the original index plus canonical VC payload.
    let reordered_results = vec![results[1].clone(), results[0].clone()];
    let reordered_bindings = vec![bindings[1].clone(), bindings[0].clone()];
    let reordered = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &reordered_results,
        None,
        &[None, None],
        &reordered_bindings,
        &[None, None],
    );
    assert!(
        reordered.iter().all(|row| row.monitor.is_none()),
        "a moved monitor binding must not donate evidence after carrier reordering",
    );
}

#[test]
fn loop_contracts_are_explicitly_unmonitored_without_inserting_iteration_monitors() {
    let function = proof_feedback_loop_function();
    let compiler_contracts = trust_types::CompilerContractBundle::new(function.contracts.clone());
    let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&function);
    let mut vcs = solver_vcs;
    vcs.extend(discharged.into_iter().map(|(vc, _)| vc));
    let mut bundle =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
    let reference =
        trust_mir_extract::contract_bundle_to_verifier_api(&function, &compiler_contracts);
    stamp_certified_monitor_metadata_from_records(
        &[],
        &monitor_reference_function(&reference),
        &reference,
        &mut bundle,
    );

    let loop_contract_ids = bundle
        .contracts
        .iter()
        .filter(|contract| {
            matches!(
                contract.kind,
                trust_verifier_api::ContractKind::LoopInvariant
                    | trust_verifier_api::ContractKind::Asserts
            )
        })
        .map(|contract| {
            let evidence = transport_monitor_evidence_from_metadata(&contract.metadata)
                .expect("every public loop clause must carry an explicit monitor decision");
            assert_eq!(evidence.status, trust_types::TransportMonitorStatus::Unmonitored);
            assert!(evidence.reason.contains("no kernel-certified monitor evidence matched"));
            contract.contract_id.clone()
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        loop_contract_ids.len(),
        2,
        "the loop invariant and decreases clauses must both remain explicitly inventoried"
    );

    let loop_obligations = bundle
        .obligations
        .iter()
        .filter(|obligation| {
            obligation
                .contract_id
                .as_ref()
                .is_some_and(|contract_id| loop_contract_ids.contains(contract_id))
        })
        .cloned()
        .collect::<Vec<_>>();
    assert!(loop_obligations.len() >= 2);
    assert_eq!(
        loop_obligations
            .iter()
            .filter_map(|obligation| obligation.contract_id.clone())
            .collect::<BTreeSet<_>>(),
        loop_contract_ids,
        "every loop clause must retain at least one exact public obligation carrier"
    );
    assert!(loop_obligations.iter().any(|obligation| {
        matches!(obligation.kind, trust_verifier_api::ObligationKind::LoopInvariant)
    }));
    assert!(loop_obligations.iter().any(|obligation| matches!(
        obligation.kind,
        trust_verifier_api::ObligationKind::Termination
    )));
    let unknown = || VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("loop-monitor-inventory-test"),
        time_ms: 0,
        reason: "the monitor inventory is independent of proof outcome".to_string(),
    };
    let results = loop_obligations
        .iter()
        .enumerate()
        .map(|(index, _)| (test_vc(610 + index as u32), unknown()))
        .collect::<Vec<_>>();
    let bindings = loop_obligations
        .iter()
        .enumerate()
        .map(|(index, obligation)| {
            result_obligation_binding(index, &results[index].0, obligation)
                .expect("loop monitor row must retain exact public obligation identity")
        })
        .map(Some)
        .collect::<Vec<_>>();
    let transport = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        None,
        &vec![None; results.len()],
        &bindings,
        &vec![None; results.len()],
    );
    for ((row, obligation), binding) in transport.iter().zip(&loop_obligations).zip(&bindings) {
        assert!(
            row.obligation_id.is_none(),
            "a monitor-only private binding must not donate public identity without the exact returned run carrier"
        );
        assert_eq!(
            row.monitor.as_ref().map(|monitor| monitor.status),
            Some(trust_types::TransportMonitorStatus::Unmonitored),
        );
        assert_eq!(
            binding.as_ref().expect("loop binding").canonical_obligation.obligation_id,
            obligation.obligation_id,
        );
    }
}

#[test]
fn verifier_returned_monitor_metadata_cannot_donate_transport_evidence() {
    let mut original_obligation = authority_test_native_obligation("monitor:no-original", 53, 53);
    stamp_monitor_metadata(
        &mut original_obligation.metadata,
        "unmonitored",
        "canonical compiler-owned monitor decision",
        &format!("sha256:{}", "b".repeat(64)),
    );
    let result = (test_vc(53), authority_test_proved());
    let binding = result_obligation_binding(0, &result.0, &original_obligation)
        .expect("serializable monitor row binding");
    assert_eq!(
        binding.monitor.as_ref().map(|monitor| monitor.evidence.status),
        Some(trust_types::TransportMonitorStatus::Unmonitored),
        "the private binding must begin with real compiler-owned monitor evidence",
    );

    // Replace the compiler-owned decision with a forged positive monitor only
    // on the verifier-returned obligation. The native identity remains exact,
    // but the returned public row no longer matches the compiler-sealed
    // canonical obligation. This proves both that monitor transport does not
    // consult returned metadata and that mutation revokes even the legitimate
    // private monitor token; it cannot retain neighboring transport authority
    // merely by preserving its IDs.
    let mut returned_obligation = original_obligation.clone();
    stamp_monitor_metadata(
        &mut returned_obligation.metadata,
        "monitored",
        "forged reflected monitor status",
        &format!("sha256:{}", "c".repeat(64)),
    );
    let run = authority_test_strict_native_run(returned_obligation);
    let results = vec![result];
    let bindings = vec![Some(binding)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    let rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&run),
        &[None],
        &bindings,
        &authorities,
    );
    assert!(rows[0].monitor.is_none());
    assert!(rows[0].obligation_id.is_none());
    assert!(rows[0].native_trust_ir.is_none());
    assert!(rows[0].proof_evidence.is_none());
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
}

#[test]
fn full_run_presence_and_public_strength_do_not_authorize_a_row() {
    let obligation = authority_test_native_obligation("authority:A", 41, 40);
    let run = authority_test_strict_native_run(obligation);
    let results = vec![(test_vc(40), authority_test_proved())];
    let cleancic = vec![None];
    let authorities = build_result_proof_authorities(&results, &[None], Some(&run), &cleancic);

    assert!(authorities.iter().all(Option::is_none));
    assert_eq!(
        trust_disposition_for_authority(
            authorities[0].as_ref(),
            0,
            &results[0].0,
            &results[0].1,
            None,
        ),
        None
    );
    assert_eq!(
        strict_l0_verification_failure(true, &results, &[None], &authorities, Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 1, skipped: 0 }),
        "a run-wide artifact bit and forged Sound/complete label must not discharge this row",
    );
}

#[test]
fn exact_identity_absent_direct_trust_vc_evidence_remains_attribution_only() {
    let obligation = authority_test_direct_trust_vc_obligation("authority:direct-trust-vc", 140);
    let run = authority_test_direct_trust_vc_run(obligation.clone());
    let results = vec![(test_vc(140), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];

    let index = build_full_verification_evidence_index(&run);
    assert!(index.strict_accepted_by_obligation_id.contains_key(obligation.obligation_id.as_str()));
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities.iter().all(Option::is_none));
}

#[test]
fn partial_or_stale_direct_trust_vc_identity_cannot_mint_authority() {
    for key in [
        "trust.trust_ir.native.verifier_suite",
        "trust.trust_ir.native.proof_unit.v1",
        "trust.trust_ir.native.future_identity",
    ] {
        let mut obligation = authority_test_direct_trust_vc_obligation(
            &format!("authority:direct-partial:{key}"),
            141,
        );
        obligation.metadata.push(trust_verifier_api::MetadataEntry {
            key: key.to_string(),
            value: "stale".to_string(),
        });
        let run = authority_test_direct_trust_vc_run(obligation.clone());
        let results = vec![(test_vc(141), authority_test_proved())];
        let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
        let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
        assert!(authorities[0].is_none(), "partial identity `{key}` minted authority");
    }
}

#[test]
fn direct_trust_vc_evidence_cannot_borrow_native_sibling_lineage() {
    let obligation =
        authority_test_direct_trust_vc_obligation("authority:direct-mixed-lineage", 142);
    let base = authority_test_direct_trust_vc_run(obligation.clone());
    let mut evidence = base.evidence[0].clone();
    evidence.artifacts.extend(authority_test_native_artifact_lineage("trust-mc", "7", "9"));
    let run = authority_test_rebuild_run(&base, vec![obligation.clone()], vec![evidence]);
    let results = vec![(test_vc(142), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];

    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities[0].is_none());
    assert!(
        build_full_verification_evidence_index(&run).strict_accepted_by_obligation_id.is_empty()
    );
}

#[test]
fn accepted_native_obligation_a_cannot_authorize_row_b() {
    let obligation = authority_test_native_obligation("authority:A", 41, 41);
    let run = authority_test_strict_native_run(obligation.clone());
    let results = vec![(test_vc(41), authority_test_proved())];
    let mut wrong_binding =
        test_binding_for_obligation(0, &results[0].0, &obligation).expect("binding");
    wrong_binding.public_obligation_id = "authority:B".to_string();
    let authorities =
        build_result_proof_authorities(&results, &[Some(wrong_binding)], Some(&run), &[None]);

    assert!(authorities.iter().all(Option::is_none), "accepted A must not be replayed onto B");
}

#[test]
fn returned_obligation_mutation_cannot_mint_entry_or_native_authority() {
    let mut canonical =
        authority_test_native_obligation("authority:canonical-returned-row", 73, 53);
    canonical.metadata.push(
        trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                vc_kind: "division_by_zero".to_string(),
                vc_index: 0,
                formula_schema: None,
            },
        )
        .to_metadata_entry()
        .expect("canonical obligation context"),
    );
    assert!(!is_definition_site_requires_marker(&canonical));

    let canonical_run = authority_test_strict_native_run(canonical.clone());
    let mut returned = canonical.clone();
    let forged_contract_id = "trust-contract:forged:requires:0".to_string();
    returned.kind = trust_verifier_api::ObligationKind::Precondition;
    returned.contract_id = Some(forged_contract_id.clone());
    mutate_test_obligation_context(&mut returned, |context| {
        context.origin = trust_verifier_api::ObligationOrigin::Contract {
            contract_id: forged_contract_id,
            contract_kind: trust_verifier_api::ContractKind::Requires,
            contract_index: 0,
            predicate_schema: None,
        };
    });
    assert!(
        is_definition_site_requires_marker(&returned),
        "the returned carrier must exercise a self-consistent forged entry-marker classification",
    );
    let returned_run =
        authority_test_rebuild_run(&canonical_run, vec![returned], canonical_run.evidence.clone());
    returned_run
        .validate_derived_state()
        .expect("mutated public carrier is internally self-consistent");
    returned_run.try_to_manifest().expect("mutated public carrier remains losslessly manifestable");

    // A constant-false compatibility placeholder makes the security impact
    // explicit: classifying from the returned context would mint an entry
    // assumption and bypass the ordinary vacuity gate. The private binding was
    // minted from the canonical non-requires row, so neither that exemption nor
    // its accepted native evidence may survive the returned-row mutation.
    let mut vc = test_vc(53);
    vc.formula = trust_types::Formula::Bool(false);
    let results = vec![(vc, authority_test_proved())];
    let binding = test_binding_for_obligation(0, &results[0].0, &canonical)
        .expect("canonical compiler binding");
    assert!(
        !binding.definition_entry_assumption,
        "a returned same-shape carrier cannot drift the already-frozen private bit",
    );
    let bindings = vec![Some(binding)];
    let authorities =
        build_result_proof_authorities(&results, &bindings, Some(&returned_run), &[None]);
    assert!(authorities.iter().all(Option::is_none));

    let transport = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&returned_run),
        &[None],
        &bindings,
        &authorities,
    );
    assert_eq!(transport[0].outcome, Outcome::RuntimeChecked);
    assert!(transport[0].monitor.is_none());
    assert!(transport[0].obligation_id.is_none());
    assert!(transport[0].native_trust_ir.is_none());
    assert!(transport[0].proof_evidence.is_none());
}

#[test]
fn serializable_valid_native_bindings_cannot_mint_or_move_authority() {
    let obligation_a = authority_test_native_obligation("authority:row-seal:A", 47, 47);
    let obligation_b = authority_test_native_obligation("authority:row-seal:B", 48, 48);
    let run_a = authority_test_strict_native_run(obligation_a.clone());
    let run_b = authority_test_strict_native_run(obligation_b.clone());
    let run = authority_test_rebuild_run(
        &run_a,
        vec![obligation_a.clone(), obligation_b.clone()],
        vec![run_a.evidence[0].clone(), run_b.evidence[0].clone()],
    );
    let results =
        vec![(test_vc(47), authority_test_proved()), (test_vc(48), authority_test_proved())];
    let bindings = vec![
        test_binding_for_obligation(0, &results[0].0, &obligation_a),
        test_binding_for_obligation(1, &results[1].0, &obligation_b),
    ];
    let correct = build_result_proof_authorities(&results, &bindings, Some(&run), &[None, None]);
    assert!(correct.iter().all(Option::is_none));

    let swapped = vec![bindings[1].clone(), bindings[0].clone()];
    let swapped_authorities =
        build_result_proof_authorities(&results, &swapped, Some(&run), &[None, None]);
    assert!(
        swapped_authorities.iter().all(Option::is_none),
        "two valid public/native bindings lose authority when moved off their sealed rows",
    );
    let transport = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&run),
        &[None, None],
        &swapped,
        &swapped_authorities,
    );
    assert!(transport.iter().all(|row| {
        row.monitor.is_none()
            && row.obligation_id.is_none()
            && row.native_trust_ir.is_none()
            && row.proof_evidence.is_none()
            && row.outcome == Outcome::RuntimeChecked
    }));
}

#[test]
fn formula_less_nonaggregate_assertion_cannot_mint_private_authority() {
    let mut obligation =
        authority_test_native_obligation("authority:formula-less-nonaggregate", 404, 404);
    obligation.kind = trust_verifier_api::ObligationKind::Assertion;
    obligation.description = "ordinary formula-less assertion".to_string();
    assert!(obligation.contract_id.is_none());
    assert!(obligation.proof_item_id.is_none());
    assert!(
        exactly_one_metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)
            .is_none()
    );
    assert!(
        exactly_one_metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .is_none()
    );

    let run = authority_test_strict_native_run(obligation.clone());
    assert_eq!(run.summary.proved, 1, "fixture must carry a public Proved label");
    let (function, _, _) = native_trust_ir_compiler_function();
    assert!(!obligation_is_synthesized_whole_function_panic_freedom(&function, None, &obligation,));
    let vc = legacy_vc_from_api_obligation(&function, &obligation);
    assert!(matches!(vc.kind, VcKind::UnsupportedMir { .. }));
    assert!(matches!(vc.formula, Formula::Bool(false)));

    let results = vec![(vc, authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities.iter().all(Option::is_none));
    assert!(matches!(
        apply_vacuity_gate_with_authority(
            0,
            &results[0].0,
            results[0].1.clone(),
            bindings[0].as_ref(),
            authorities[0].as_ref(),
        ),
        VerificationResult::Unknown { .. }
    ));
}

#[test]
fn grounded_panic_freedom_revokes_public_binding_then_rebuilds_kernel_authority() {
    let mut catchall = test_vc(49);
    catchall.kind = VcKind::Assertion { message: "panic freedom: test::f".to_string() };
    catchall.formula =
        trust_types::Formula::Var("panic_reachable:test::f".to_string(), trust_types::Sort::Bool);
    let mut residual = test_vc(50);
    residual.formula = trust_types::Formula::Eq(
        Box::new(trust_types::Formula::Int(0)),
        Box::new(trust_types::Formula::Int(1)),
    );
    let mut results = vec![
        (catchall.clone(), authority_test_proved()),
        (residual.clone(), authority_test_proved()),
    ];
    let catchall_obligation = authority_test_native_obligation("authority:grounded-panic", 49, 49);
    let residual_obligation =
        authority_test_native_obligation("authority:grounded-residual", 50, 50);
    let mut bindings = vec![
        test_binding_for_obligation(0, &results[0].0, &catchall_obligation),
        test_binding_for_obligation(1, &results[1].0, &residual_obligation),
    ];

    let grounded = ground_panic_freedom_catchall(&mut results, Some(&mut bindings))
        .expect("the controlled rewrite must return its exact grounding record");

    assert_eq!(results[0].0.formula, residual.formula);
    assert_eq!(grounded.0, catchall_obligation.obligation_id);
    assert_eq!(grounded.1, exact_result_row_identity(0, &results[0].0).unwrap());
    assert!(
        bindings[0].is_none(),
        "public/native evidence for the opaque catch-all must not follow its grounded rewrite"
    );
    assert!(bindings[1].as_ref().is_some_and(|binding| binding.matches_row(1, &results[1].0)));
    let cleancic = certify_all(&results, None);
    assert!(matches!(cleancic[0].as_ref(), Some(trust_ir::ProofEvidence::CleanCic { .. })));
    let authorities = build_result_proof_authorities(&results, &bindings, None, &cleancic);
    assert!(matches!(authorities[0].as_ref(), Some(ResultProofAuthority::KernelCertified { .. })));
}

#[test]
fn grounded_panic_freedom_does_not_repair_a_swapped_binding() {
    let mut catchall = test_vc(51);
    catchall.kind = VcKind::Assertion { message: "panic freedom: test::f".to_string() };
    catchall.formula =
        trust_types::Formula::Var("panic_reachable:test::f".to_string(), trust_types::Sort::Bool);
    let mut residual = test_vc(52);
    // Exercise the equality no-op edge too: stale validation must happen
    // before deciding that the replacement formula is unchanged.
    residual.formula = catchall.formula.clone();
    let mut results =
        vec![(catchall.clone(), authority_test_proved()), (residual, authority_test_proved())];
    let obligation_a = authority_test_native_obligation("authority:stale-ground:A", 51, 51);
    let obligation_b = authority_test_native_obligation("authority:stale-ground:B", 52, 52);
    let binding_a = test_binding_for_obligation(0, &results[0].0, &obligation_a);
    let binding_b = test_binding_for_obligation(1, &results[1].0, &obligation_b);
    let mut swapped = vec![binding_b, binding_a];

    let grounded = ground_panic_freedom_catchall(&mut results, Some(&mut swapped));

    assert_eq!(
        results[0].0.formula, catchall.formula,
        "a stale binding must make the controlled rewrite fail closed"
    );
    assert!(swapped[0].is_none(), "the stale binding must be revoked, not resealed");
    assert!(grounded.is_none(), "a rejected rewrite must not mint a grounding record");
}

#[test]
fn grounded_panic_freedom_identity_cannot_cross_authorize_same_index_in_another_function() {
    let mut grounded_vc = test_vc(53);
    grounded_vc.function = trust_types::Symbol::intern("test::grounded");
    grounded_vc.kind = VcKind::Assertion { message: "panic freedom: grounded".to_string() };
    grounded_vc.formula = trust_types::Formula::Eq(
        Box::new(trust_types::Formula::Int(0)),
        Box::new(trust_types::Formula::Int(1)),
    );
    let grounded_identity =
        exact_result_row_identity(0, &grounded_vc).expect("fixture row must canonicalize");
    let mut records = FxHashMap::default();
    records.insert("authority:grounded:first".to_string(), grounded_identity);

    assert!(row_was_compiler_grounded_in(&records, 0, &grounded_vc));

    let mut unrelated = grounded_vc.clone();
    unrelated.function = trust_types::Symbol::intern("test::unrelated");
    assert!(
        !row_was_compiler_grounded_in(&records, 0, &unrelated),
        "per-function row zero must not inherit another function's grounding authority"
    );

    unrelated.function = grounded_vc.function.clone();
    unrelated.formula = trust_types::Formula::Bool(true);
    assert!(
        !row_was_compiler_grounded_in(&records, 0, &unrelated),
        "a changed formula at the same function/index must not inherit grounding authority"
    );
}

#[test]
fn duplicate_public_obligation_ids_are_ambiguous_and_fail_closed() {
    let obligation = authority_test_native_obligation("authority:duplicate", 41, 41);
    let mut run = authority_test_strict_native_run(obligation.clone());
    run.requested_obligations.push(obligation.clone());
    run.requested_obligations.push(obligation.clone());

    let results = vec![(test_vc(41), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities.iter().all(Option::is_none));

    let rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&run),
        &[None],
        &bindings,
        &authorities,
    );
    assert!(rows[0].monitor.is_none());
    assert!(
        rows[0].obligation_id.is_none(),
        "an ambiguous native binding must remain unattributed, not be laundered into a legacy id"
    );
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
    assert!(rows[0].native_trust_ir.is_none());
    assert!(rows[0].proof_evidence.is_none());
}

#[test]
fn public_native_evidence_decision_cannot_authorize_transport() {
    let obligation = authority_test_native_obligation("authority:accepted-evidence", 43, 43);
    let run = authority_test_strict_native_run(obligation.clone());
    let mut noise = run.evidence[0].clone();
    noise.evidence_id = "authority:noise-first".to_string();
    noise.status = trust_verifier_api::EvidenceStatus::Unknown;
    noise.proof_strength = None;
    noise.artifacts.clear();
    noise.diagnostics = vec!["unrelated first evidence row".to_string()];
    let run = authority_test_rebuild_run(
        &run,
        vec![obligation.clone()],
        vec![noise, run.evidence[0].clone()],
    );

    let results = vec![(test_vc(43), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities[0].is_none());

    let rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&run),
        &[None],
        &bindings,
        &authorities,
    );
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
    assert!(rows[0].proof_evidence.is_none());
    assert!(
        rows[0].native_trust_ir.as_ref().is_some_and(|identity| identity.present),
        "native identity remains attribution even though it grants no proved outcome or proof evidence",
    );
}

#[test]
fn same_obligation_proved_failed_conflict_cannot_mint_compiler_authority() {
    let obligation = authority_test_native_obligation("authority:proved-failed-conflict", 54, 54);
    let proved_run = authority_test_strict_native_run(obligation.clone());
    let proved = proved_run.evidence[0].clone();
    let failed = trust_verifier_api::ObligationEvidence {
        evidence_id: "authority:proved-failed-conflict:failed".to_string(),
        obligation_id: obligation.obligation_id.clone(),
        engine: proved.engine.clone(),
        status: trust_verifier_api::EvidenceStatus::Failed,
        proof_strength: None,
        artifacts: Vec::new(),
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: vec!["independent refutation of the same obligation".to_string()],
    };
    let run =
        authority_test_rebuild_run(&proved_run, vec![obligation.clone()], vec![proved, failed]);
    run.validate_derived_state().expect("conflicting evidence run remains canonical");
    let manifest = run.to_manifest();
    assert!(manifest.accepted_evidence.iter().any(|decision| {
        decision.obligation_id == obligation.obligation_id
            && decision.status == trust_verifier_api::EvidenceStatus::Proved
    }));
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == obligation.obligation_id
            && decision.status == trust_verifier_api::EvidenceStatus::Failed
    }));

    let index = build_full_verification_evidence_index(&run);
    assert!(index.evidence_by_obligation_id.is_empty());
    assert!(index.strict_accepted_by_obligation_id.is_empty());
    let results = vec![(test_vc(54), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities[0].is_none());
    let transport = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&run),
        &[None],
        &bindings,
        &authorities,
    );
    assert_ne!(transport[0].outcome, Outcome::Proved);
    assert!(transport[0].proof_evidence.is_none());
}

#[test]
fn duplicate_evidence_ids_cannot_mint_a_strict_native_token() {
    let obligation = authority_test_native_obligation("authority:duplicate-evidence", 44, 44);
    let mut run = authority_test_strict_native_run(obligation.clone());
    let duplicate = run.evidence[0].clone();
    run.evidence.push(duplicate);

    let results = vec![(test_vc(44), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities.iter().all(Option::is_none));
}

#[test]
fn multiple_accepted_evidence_decisions_are_ambiguous_and_fail_closed() {
    let obligation = authority_test_native_obligation("authority:multiple-accepted", 45, 45);
    let run = authority_test_strict_native_run(obligation.clone());
    let mut second = run.evidence[0].clone();
    second.evidence_id = "authority:second-accepted".to_string();
    let run = authority_test_rebuild_run(
        &run,
        vec![obligation.clone()],
        vec![run.evidence[0].clone(), second],
    );

    let results = vec![(test_vc(45), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities.iter().all(Option::is_none));
    assert!(strict_full_verification_accepted_obligation_ids(&run).is_empty());
}

#[test]
fn native_artifact_fragments_from_different_lineages_cannot_mint_authority() {
    let obligation = authority_test_native_obligation("authority:split-lineage", 46, 46);
    let mut run = authority_test_strict_native_run(obligation.clone());
    let bundle_digest = run.evidence[0]
        .artifacts
        .iter()
        .find(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::EngineInput
                && artifact
                    .uri
                    .strip_prefix("trust_ir-native://verification-bundle/")
                    .is_some_and(|tail| !tail.contains('/'))
        })
        .expect("fixture bundle artifact")
        .hash
        .value
        .clone();
    let request_artifact = run.evidence[0]
        .artifacts
        .iter_mut()
        .find(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::EngineInput
                && artifact.uri.contains("/trust-mc/request/")
        })
        .expect("fixture request artifact");
    request_artifact.uri = request_artifact.uri.replacen(&bundle_digest, &"d".repeat(64), 1);

    let results = vec![(test_vc(46), authority_test_proved())];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, &obligation)];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &[None]);
    assert!(authorities.iter().all(Option::is_none));
}

#[test]
fn same_span_public_native_rows_cannot_mint_or_cross_transport_authority() {
    let obligation_a = authority_test_native_obligation("authority:A", 41, 42);
    let run = authority_test_strict_native_run(obligation_a.clone());
    let obligation_b = authority_test_native_obligation("authority:B", 42, 42);
    let run = authority_test_rebuild_run(
        &run,
        vec![obligation_a.clone(), obligation_b.clone()],
        run.evidence.clone(),
    );

    let results =
        vec![(test_vc(42), authority_test_proved()), (test_vc(42), authority_test_proved())];
    let bindings = vec![
        test_binding_for_obligation(0, &results[0].0, &obligation_a),
        test_binding_for_obligation(1, &results[1].0, &obligation_b),
    ];
    let cleancic = vec![None, None];
    let authorities = build_result_proof_authorities(&results, &bindings, Some(&run), &cleancic);
    assert!(authorities.iter().all(Option::is_none));

    assert_eq!(
        strict_l0_verification_failure(true, &results, &bindings, &authorities, Some(&run)),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 2, skipped: 0 }),
        "neither serializable public row may become compiler authority",
    );

    let rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&run),
        &cleancic,
        &bindings,
        &authorities,
    );
    assert_eq!(rows[0].obligation_id.as_deref(), Some("authority:A"));
    assert_eq!(rows[0].outcome, Outcome::RuntimeChecked);
    assert!(rows[0].proof_evidence.is_none());
    assert_eq!(rows[1].obligation_id.as_deref(), Some("authority:B"));
    assert_eq!(rows[1].outcome, Outcome::RuntimeChecked);
    assert!(rows[1].proof_evidence.is_none());

    // Rebuilding the public bindings for a reordered result carrier without
    // rebuilding its private authority vector must not let A's token donate
    // either a proved outcome or A's accepted proof evidence to the
    // structurally-identical B row.
    let reordered_results = vec![results[1].clone(), results[0].clone()];
    let reordered_bindings = vec![
        test_binding_for_obligation(0, &reordered_results[0].0, &obligation_b),
        test_binding_for_obligation(1, &reordered_results[1].0, &obligation_a),
    ];
    let reordered = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &reordered_results,
        Some(&run),
        &cleancic,
        &reordered_bindings,
        &authorities,
    );
    assert_eq!(reordered[0].obligation_id.as_deref(), Some("authority:B"));
    assert_eq!(reordered[0].outcome, Outcome::RuntimeChecked);
    assert!(reordered[0].proof_evidence.is_none());
    assert_eq!(reordered[1].obligation_id.as_deref(), Some("authority:A"));
    assert_eq!(reordered[1].outcome, Outcome::RuntimeChecked);
    assert!(reordered[1].proof_evidence.is_none());
}

#[test]
fn cleancic_authority_is_exactly_index_bound_without_native_token() {
    let results =
        vec![(test_vc(43), authority_test_proved()), (test_vc(44), authority_test_proved())];
    let cleancic = vec![None, Some(authority_test_clean_cic(7))];
    let authorities = build_result_proof_authorities(&results, &[], None, &cleancic);

    assert!(authorities[0].is_none());
    assert_eq!(
        trust_disposition_for_authority(
            authorities[1].as_ref(),
            1,
            &results[1].0,
            &results[1].1,
            None,
        ),
        Some((TrustStatus::Certified, TrustProofStrength::Constructive)),
    );
}

#[test]
fn kernel_authority_cannot_move_to_another_row_or_survive_reordering() {
    let results =
        vec![(test_vc(47), authority_test_proved()), (test_vc(48), authority_test_proved())];
    let authorities = build_result_proof_authorities(
        &results,
        &[],
        None,
        &[None, Some(authority_test_clean_cic(8))],
    );
    let authority = authorities[1].as_ref().expect("second row kernel authority");
    assert!(authority.is_static_proof_for(1, &results[1].0, &results[1].1, None));
    assert!(!authority.is_static_proof_for(0, &results[1].0, &results[1].1, None));
    assert!(!authority.is_static_proof_for(1, &results[0].0, &results[0].1, None));

    let reordered = vec![results[1].clone(), results[0].clone()];
    let rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &reordered,
        None,
        &[None, Some(authority_test_clean_cic(8))],
        &[],
        &[authorities[1].clone(), authorities[0].clone()],
    );
    assert_ne!(rows[0].outcome, Outcome::Proved);
    assert_ne!(rows[1].outcome, Outcome::Proved);
    assert!(rows.iter().all(|row| row.proof_evidence.is_none()));
}

#[test]
fn duplicate_structural_rows_still_have_distinct_kernel_authority() {
    let vc = test_vc(49);
    let results = vec![(vc.clone(), authority_test_proved()), (vc, authority_test_proved())];
    let authorities = build_result_proof_authorities(
        &results,
        &[],
        None,
        &[Some(authority_test_clean_cic(9)), None],
    );
    let authority = authorities[0].as_ref().expect("first row kernel authority");
    assert!(authority.is_static_proof_for(0, &results[0].0, &results[0].1, None));
    assert!(!authority.is_static_proof_for(1, &results[1].0, &results[1].1, None));
}

#[test]
fn strict_l0_verification_ignores_non_l0_unknowns() {
    let mut postcondition = test_vc(10);
    postcondition.kind = VcKind::Postcondition;
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-wp"),
        time_ms: 1,
        reason: "not enough invariants".to_string(),
    };

    assert_eq!(
        strict_l0_verification_failure(true, &[(postcondition, unknown)], &[], &[], None),
        None
    );
}

// Trust (#47/#48): a known-panicking unmodeled call (`o.unwrap()`) emits an
// `UnsupportedMir` obligation that the full-verifier router has no owner for, so it
// returns UNKNOWN. Full mode rejects every non-proved outcome; this narrower
// classifier additionally records the known reachable panic as a REFUTATION
// instead of a generic capability gap.
#[test]
fn strict_l0_verification_refutes_known_panicking_unsupported_call() {
    // The round-tripped (full-lane) representation: the original
    // `Call::unwrap::panic-freedom-unverified` kind is preserved inside `detail`.
    let mut unwrap_vc = test_vc(20);
    unwrap_vc.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::trust.vc::unsupported_mir".to_string(),
        detail: "unsupported MIR `Call::unwrap::panic-freedom-unverified`: bb0: `unwrap` \
                 panics on None/Err and its panic-freedom is not modeled"
            .to_string(),
    };
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "no full-verification primary owner is defined for obligation kind \
                 Custom { namespace: \"trust.vc\", name: \"unsupported_mir\" }"
            .to_string(),
    };
    // The known-panicking unsupported call is counted as `failed` so reports
    // preserve the concrete refutation classification.
    assert_eq!(
        strict_l0_verification_failure(true, &[(unwrap_vc, unknown.clone())], &[], &[], None),
        Some(FullVerificationFailure { failed: 1, unknown: 0, runtime_checked: 0, skipped: 0 }),
    );

    // The direct (default-lane) representation: the marker lives in `kind`. Same verdict.
    let mut direct_vc = test_vc(21);
    direct_vc.kind = VcKind::UnsupportedMir {
        kind: "Call::expect::panic-freedom-unverified".to_string(),
        detail: "bb0: `expect` panics on None/Err".to_string(),
    };
    assert_eq!(
        strict_l0_verification_failure(true, &[(direct_vc, unknown.clone())], &[], &[], None),
        Some(FullVerificationFailure { failed: 1, unknown: 0, runtime_checked: 0, skipped: 0 }),
    );
}

// Trust (#47/#48 soundness boundary): a GENERIC `UnsupportedMir` (no
// `panic-freedom-unverified` marker — e.g. an unmodeled std construct the solver
// returns UNKNOWN for) is a benign coverage gap, NOT a refutation. It must stay
// `unknown` so the `-full` gate does not over-reject valid Rust.
#[test]
fn strict_l0_verification_keeps_generic_unsupported_mir_as_unknown() {
    let mut generic_vc = test_vc(22);
    generic_vc.kind = VcKind::UnsupportedMir {
        kind: "Rvalue::Cast".to_string(),
        detail: "unmodeled cast shape".to_string(),
    };
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "unsupported".to_string(),
    };
    assert_eq!(
        strict_l0_verification_failure(true, &[(generic_vc, unknown)], &[], &[], None),
        Some(FullVerificationFailure { failed: 0, unknown: 1, runtime_checked: 0, skipped: 0 }),
    );
}

// Trust: fail-closed on absent-callee panic (revert of d8a9bbc28e fail-open;
// unproven panic MUST fail closed). A STRICT-L0 SAFETY obligation the native typed
// lane could not model (`x.pow(20)`'s repeated-mul → trust-mc Unsupported) round-
// trips as `UnsupportedMir{FullVerification::ArithmeticSafety}` and returns Unknown.
// Before the fail-soft bundle change this failed the whole native bundle → the #48
// lowering-failure guard aborted; after, it was a non-fatal Unknown, so
// `{ let x=(a as u32)+1; x.pow(20) }` verified with exit 0 while overflowing.
// `strict_l0_verification_failure` now reclassifies it to `failed` so the strict-L0
// abort fires — fail-closed restored.
#[test]
fn strict_l0_verification_refutes_native_unsupported_safety_obligation() {
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "native full verifier evidence status: Unsupported; ... primary evidence \
                 was unsupported"
            .to_string(),
    };
    // The `x.pow(20)` Mul-overflow obligation: kind carries the native round-trip
    // `FullVerification::ArithmeticSafety` prefix.
    let mut pow_vc = test_vc(30);
    pow_vc.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "arithmetic overflow (Mul)".to_string(),
    };
    assert_eq!(
        strict_l0_verification_failure(true, &[(pow_vc, unknown.clone())], &[], &[], None),
        Some(FullVerificationFailure { failed: 1, unknown: 0, runtime_checked: 0, skipped: 0 }),
    );

    // A BoundsCheck twin (an OOB index the native lane could not discharge) is
    // likewise reclassified to `failed`.
    let mut bounds_vc = test_vc(31);
    bounds_vc.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::BoundsCheck".to_string(),
        detail: "slice index out of bounds".to_string(),
    };
    assert_eq!(
        strict_l0_verification_failure(true, &[(bounds_vc, unknown.clone())], &[], &[], None),
        Some(FullVerificationFailure { failed: 1, unknown: 0, runtime_checked: 0, skipped: 0 }),
    );

    // SOUNDNESS: a PROVED safety obligation (an engine discharged it) is never
    // reclassified — the reclassification only fires on a non-`Proved` verdict.
    let mut proved_pow = test_vc(32);
    proved_pow.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "arithmetic overflow (Mul)".to_string(),
    };
    let proved = VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let failure = strict_l0_verification_failure(true, &[(proved_pow, proved)], &[], &[], None);
    // Not full-verifier-backed + Proved on an UnsupportedMir VC → counted `unknown`
    // (no runtime fallback), NEVER `failed`. The key assertion is `failed == 0`.
    assert_eq!(failure.map(|f| f.failed), Some(0));

    // A non-safety `FullVerification::Postcondition` UnsupportedMir stays a coverage
    // gap — the discriminator is scoped to L0 SAFETY kinds only.
    let mut postcond_vc = test_vc(33);
    postcond_vc.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::Postcondition".to_string(),
        detail: "postcondition not modeled".to_string(),
    };
    assert!(!is_native_unsupported_strict_l0_safety_mir(&postcond_vc.kind));
}

#[test]
fn v1_bridge_requires_exact_bound_semantics_not_just_span() {
    let mut native_placeholder = test_vc(34);
    native_placeholder.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "typed-CHC left noOverflow_add unsupported".to_string(),
    };
    let native_unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "native arithmetic safety was unsupported".to_string(),
    };

    let mut precise = test_vc(34);
    precise.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::i128(), trust_types::Ty::i128()),
    };
    let atom = trust_types::Formula::Var("overflow_reachable".to_string(), trust_types::Sort::Bool);
    precise.formula =
        trust_types::Formula::And(vec![atom.clone(), trust_types::Formula::Not(Box::new(atom))]);
    // The API row retained this exact typed violation formula even though its
    // cross-lane kind is the generic FullVerification label.
    native_placeholder.formula = precise.formula.clone();
    let obligation = authority_test_native_obligation("bridge:exact", 34, 34);
    let mut bindings = vec![test_binding_for_obligation(0, &native_placeholder, &obligation)];

    let (bridged, proved, failed, eligibilities) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        std::slice::from_ref(&precise),
        &mut bindings,
        vec![(native_placeholder, native_unknown)],
    );

    assert_eq!(proved, 1, "the exact bound semantic VC must reach the ay bridge");
    assert_eq!(failed, 0);
    assert!(matches!(bridged[0].1, VerificationResult::Proved { .. }));
    assert!(
        exact_vc_key(&bridged[0].0) == exact_vc_key(&precise),
        "bridge must retain the real VC, not the placeholder"
    );
    assert!(
        eligibilities[0].as_ref().is_some_and(|eligibility| {
            eligibility.row
                == exact_result_row_identity(0, &bridged[0].0).expect("exact bridged row")
        }),
        "a fresh strict local AY proof must mint exact private S1 eligibility"
    );

    // Anti-no-op: consume that authentic bridge-minted capability through a
    // distinct, injected strict fresh revalidation and prove the compiler
    // actually mints the intended row authority and reporting tier.
    let cleancic = vec![None];
    let fixed_now = std::time::Instant::now();
    let mut budgets = Vec::new();
    let receipts = revalidate_all_solver_proofs_with(
        &bridged,
        &eligibilities,
        &cleancic,
        None,
        || fixed_now,
        |formula, budget_ms| {
            budgets.push(budget_ms);
            Some(StrictSmtRevalidation {
                canonical_problem: trust_router::in_process_ay_backend::problem_smt2(formula),
                problem_sha256: "a".repeat(64),
                time_ms: 7,
            })
        },
    );
    assert_eq!(budgets, vec![4_000], "an unbounded function still caps each S1 solve");
    assert!(receipts[0].is_some());
    let authorities = build_result_proof_authorities_with_revalidations(
        &bridged, &bindings, None, &cleancic, &receipts,
    );
    assert!(matches!(authorities[0], Some(ResultProofAuthority::SolverRevalidated { .. })));
    assert_eq!(
        trust_disposition_for_authority(
            authorities[0].as_ref(),
            0,
            &bridged[0].0,
            &bridged[0].1,
            bindings[0].as_ref(),
        ),
        Some((TrustStatus::Trusted, TrustProofStrength::SmtUnsat)),
    );
    let proof_results = build_proof_results_with_runtime_checks(
        false,
        &bridged,
        &[],
        &bindings,
        &authorities,
        None,
    );
    let disposition = proof_results.dispositions.iter().next().expect("S1 disposition");
    assert_eq!(disposition.status, TrustStatus::Trusted);
    assert_eq!(disposition.strength, TrustProofStrength::SmtUnsat);
    assert!(!disposition.certified, "trusted AY replay is not a Clean certification");
    assert!(
        !authorities[0].as_ref().expect("S1 authority").is_kernel_proof_for(
            0,
            &bridged[0].0,
            bindings[0].as_ref(),
        ),
        "S1 must not become E4/E5 kernel authority"
    );
    assert!(
        !authorities[0].as_ref().expect("S1 authority").is_exact_source_clause_body_proof_for(
            0,
            &bridged[0].0,
            &bridged[0].1,
            bindings[0].as_ref(),
        ),
        "S1 must not recursively feed source-clause authority"
    );
}

fn s1_test_row(line: u32, atom_name: &str) -> (VerificationCondition, VerificationResult) {
    let mut vc = test_vc(line);
    let atom = trust_types::Formula::Var(atom_name.to_string(), trust_types::Sort::Bool);
    vc.formula =
        trust_types::Formula::And(vec![atom.clone(), trust_types::Formula::Not(Box::new(atom))]);
    (vc, authority_test_proved())
}

fn s1_test_eligibility(index: usize, vc: &VerificationCondition) -> SolverRevalidationEligibility {
    SolverRevalidationEligibility {
        row: exact_result_row_identity(index, vc).expect("serializable S1 test row"),
        producer_canonical_problem: trust_router::in_process_ay_backend::problem_smt2(&vc.formula),
    }
}

fn s1_test_strict_result(formula: &trust_types::Formula) -> StrictSmtRevalidation {
    StrictSmtRevalidation {
        canonical_problem: trust_router::in_process_ay_backend::problem_smt2(formula),
        problem_sha256: "b".repeat(64),
        time_ms: 3,
    }
}

#[test]
fn s1_revalidation_rejects_carrier_skew_swaps_kernel_and_public_provenance() {
    let results = vec![s1_test_row(201, "s1_a"), s1_test_row(202, "s1_b")];
    let eligibilities = vec![
        Some(s1_test_eligibility(0, &results[0].0)),
        Some(s1_test_eligibility(1, &results[1].0)),
    ];
    let no_kernel = vec![None, None];
    let fixed_now = std::time::Instant::now();

    // Exact length is a precondition for the whole positional carrier. Neither
    // skew invokes the injected solver, and both return all-None at result
    // cardinality rather than accepting a valid-looking prefix.
    for (short_eligibility, short_cleancic) in [(true, false), (false, true)] {
        let mut calls = 0;
        let receipts = revalidate_all_solver_proofs_with(
            &results,
            if short_eligibility { &eligibilities[..1] } else { &eligibilities },
            if short_cleancic { &no_kernel[..1] } else { &no_kernel },
            None,
            || fixed_now,
            |formula, _| {
                calls += 1;
                Some(s1_test_strict_result(formula))
            },
        );
        assert_eq!(receipts, vec![None, None]);
        assert_eq!(calls, 0, "length skew must be rejected before any solve");
    }
    let mut extra_eligibility = eligibilities.clone();
    extra_eligibility.push(None);
    let mut calls = 0;
    let extra = revalidate_all_solver_proofs_with(
        &results,
        &extra_eligibility,
        &no_kernel,
        None,
        || fixed_now,
        |formula, _| {
            calls += 1;
            Some(s1_test_strict_result(formula))
        },
    );
    assert_eq!(extra, vec![None, None]);
    assert_eq!(calls, 0, "an extra positional capability also rejects the whole lane");

    let mut swapped = eligibilities.clone();
    swapped.swap(0, 1);
    let mut calls = 0;
    let receipts = revalidate_all_solver_proofs_with(
        &results,
        &swapped,
        &no_kernel,
        None,
        || fixed_now,
        |formula, _| {
            calls += 1;
            Some(s1_test_strict_result(formula))
        },
    );
    assert_eq!(receipts, vec![None, None]);
    assert_eq!(calls, 0, "swapped exact row capabilities must not reach AY");

    let mut stale = eligibilities.clone();
    stale[0].as_mut().expect("first eligibility").producer_canonical_problem.push(' ');
    let mut solved_formulas = Vec::new();
    let receipts = revalidate_all_solver_proofs_with(
        &results,
        &stale,
        &no_kernel,
        None,
        || fixed_now,
        |formula, _| {
            solved_formulas.push(formula.clone());
            Some(s1_test_strict_result(formula))
        },
    );
    assert!(receipts[0].is_none());
    assert!(receipts[1].is_some());
    assert_eq!(solved_formulas, vec![results[1].0.formula.clone()]);

    // A CleanCIC row is already stronger and must not spend an SMT query. The
    // neighboring eligible row still runs, proving this is an exact per-row
    // skip rather than an accidental all-none short circuit.
    let cleancic = vec![Some(authority_test_clean_cic(201)), None];
    let mut solved_formulas = Vec::new();
    let receipts = revalidate_all_solver_proofs_with(
        &results,
        &eligibilities,
        &cleancic,
        None,
        || fixed_now,
        |formula, _| {
            solved_formulas.push(formula.clone());
            Some(s1_test_strict_result(formula))
        },
    );
    assert!(receipts[0].is_none());
    assert!(receipts[1].is_some());
    assert_eq!(solved_formulas, vec![results[1].0.formula.clone()]);

    // Hostile public attribution is inert without the private producer
    // carrier: local-looking, cached, native CHC/PDR/WP, structural, and
    // bounded labels all remain ineligible and cause zero solves.
    let hostile_names = [
        "ay-in-process",
        "cached:ay-in-process",
        "trust-vc",
        "trust-mc-pdr",
        "trust-wp",
        "trust-full-verifier",
        "trust-structural",
        "bounded-finite",
    ];
    let hostile = hostile_names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            let (vc, mut result) = s1_test_row(220 + index as u32, name);
            let VerificationResult::Proved { solver, proof_certificate, .. } = &mut result else {
                unreachable!()
            };
            *solver = trust_types::Symbol::intern(name);
            *proof_certificate = Some(format!("public evidence from {name}").into_bytes());
            (vc, result)
        })
        .collect::<Vec<_>>();
    let hostile_eligibilities = vec![None; hostile.len()];
    let hostile_cleancic = vec![None; hostile.len()];
    let mut calls = 0;
    let receipts = revalidate_all_solver_proofs_with(
        &hostile,
        &hostile_eligibilities,
        &hostile_cleancic,
        None,
        || fixed_now,
        |formula, _| {
            calls += 1;
            Some(s1_test_strict_result(formula))
        },
    );
    assert!(receipts.iter().all(Option::is_none));
    assert_eq!(calls, 0, "public/cached/native/structural labels are not eligibility");
    let authorities = build_result_proof_authorities_with_revalidations(
        &hostile,
        &[],
        None,
        &hostile_cleancic,
        &receipts,
    );
    assert!(authorities.iter().all(Option::is_none));

    // Even an aligned private capability cannot survive if the ordinary row is
    // later relabeled as a bounded, exhaustive-finite, or structural proof.
    // Public strength is reject-only here: matching it never creates the
    // capability, while a non-strict shape revokes one before the fresh solve.
    let mut non_strict = vec![
        s1_test_row(231, "bounded"),
        s1_test_row(232, "finite"),
        s1_test_row(233, "structural"),
    ];
    let strengths = [
        trust_types::ProofStrength::bounded(8),
        trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::ExhaustiveFinite(4),
            assurance: trust_types::AssuranceLevel::Sound,
        },
        trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::AbstractInterpretation,
            assurance: trust_types::AssuranceLevel::Sound,
        },
    ];
    for ((_, result), strength) in non_strict.iter_mut().zip(strengths) {
        let VerificationResult::Proved { strength: current, .. } = result else { unreachable!() };
        *current = strength;
    }
    let non_strict_eligibilities = non_strict
        .iter()
        .enumerate()
        .map(|(index, (vc, _))| Some(s1_test_eligibility(index, vc)))
        .collect::<Vec<_>>();
    let non_strict_cleancic = vec![None; non_strict.len()];
    let mut calls = 0;
    let receipts = revalidate_all_solver_proofs_with(
        &non_strict,
        &non_strict_eligibilities,
        &non_strict_cleancic,
        None,
        || fixed_now,
        |formula, _| {
            calls += 1;
            Some(s1_test_strict_result(formula))
        },
    );
    assert!(receipts.iter().all(Option::is_none));
    assert_eq!(calls, 0, "non-strict producer rows cannot inherit S1 eligibility");
}

#[test]
fn s1_receipts_are_byte_and_position_bound_before_authority_mint() {
    let results = vec![s1_test_row(241, "receipt_a"), s1_test_row(242, "receipt_b")];
    let eligibilities = vec![
        Some(s1_test_eligibility(0, &results[0].0)),
        Some(s1_test_eligibility(1, &results[1].0)),
    ];
    let cleancic = vec![None, None];
    let fixed_now = std::time::Instant::now();
    let receipts = revalidate_all_solver_proofs_with(
        &results,
        &eligibilities,
        &cleancic,
        None,
        || fixed_now,
        |formula, _| Some(s1_test_strict_result(formula)),
    );
    assert!(receipts.iter().all(Option::is_some));
    for (index, receipt) in receipts.iter().enumerate() {
        let receipt = receipt.as_ref().expect("fresh receipt");
        assert_eq!(receipt.row_index, index);
        assert_eq!(
            receipt.canonical_vc.as_bytes(),
            canonical_exact_vc_payload(&results[index].0).expect("canonical VC").as_bytes(),
        );
    }
    let authorities = build_result_proof_authorities_with_revalidations(
        &results,
        &[],
        None,
        &cleancic,
        &receipts,
    );
    assert!(authorities.iter().all(|authority| matches!(
        authority,
        Some(ResultProofAuthority::SolverRevalidated { .. })
    )));

    let mut swapped = receipts.clone();
    swapped.swap(0, 1);
    let swapped_authorities =
        build_result_proof_authorities_with_revalidations(&results, &[], None, &cleancic, &swapped);
    assert!(swapped_authorities.iter().all(Option::is_none));

    let mut stale_payload = receipts.clone();
    stale_payload[0].as_mut().expect("first receipt").canonical_vc.push(' ');
    let stale_authorities = build_result_proof_authorities_with_revalidations(
        &results,
        &[],
        None,
        &cleancic,
        &stale_payload,
    );
    assert!(stale_authorities[0].is_none());
    assert!(matches!(stale_authorities[1], Some(ResultProofAuthority::SolverRevalidated { .. })));

    let truncated_authorities = build_result_proof_authorities_with_revalidations(
        &results,
        &[],
        None,
        &cleancic,
        &receipts[..1],
    );
    assert!(truncated_authorities.iter().all(Option::is_none));
}

#[test]
fn s1_revalidation_clamps_remaining_budget_and_discards_late_success() {
    let results = vec![s1_test_row(261, "deadline")];
    let eligibilities = vec![Some(s1_test_eligibility(0, &results[0].0))];
    let cleancic = vec![None];
    let start = std::time::Instant::now();
    let deadline = start + std::time::Duration::from_millis(250);
    let mut times = [start, start + std::time::Duration::from_millis(1)].into_iter();
    let mut budgets = Vec::new();
    let receipts = revalidate_all_solver_proofs_with(
        &results,
        &eligibilities,
        &cleancic,
        Some(deadline),
        || times.next().expect("pre/post clock sample"),
        |formula, budget_ms| {
            budgets.push(budget_ms);
            Some(s1_test_strict_result(formula))
        },
    );
    assert_eq!(budgets, vec![250], "solve budget is min(4s, deadline remaining)");
    assert!(receipts[0].is_some());

    let late_deadline = start + std::time::Duration::from_millis(100);
    let mut late_times = [start, start + std::time::Duration::from_millis(101)].into_iter();
    let mut calls = 0;
    let late = revalidate_all_solver_proofs_with(
        &results,
        &eligibilities,
        &cleancic,
        Some(late_deadline),
        || late_times.next().expect("pre/post late clock sample"),
        |formula, budget_ms| {
            calls += 1;
            assert_eq!(budget_ms, 100);
            Some(s1_test_strict_result(formula))
        },
    );
    assert_eq!(calls, 1);
    assert_eq!(late, vec![None], "a strict success returned after deadline is inert");

    let mut preexpired_calls = 0;
    let preexpired = revalidate_all_solver_proofs_with(
        &results,
        &eligibilities,
        &cleancic,
        Some(start),
        || start,
        |formula, _| {
            preexpired_calls += 1;
            Some(s1_test_strict_result(formula))
        },
    );
    assert_eq!(preexpired, vec![None]);
    assert_eq!(preexpired_calls, 0, "expired deadline rejects before solve");
}

#[test]
fn v1_bridge_cannot_reseal_two_swapped_valid_bindings() {
    let mut native_a = test_vc(37);
    native_a.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "row A placeholder".to_string(),
    };
    let mut native_b = test_vc(38);
    native_b.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "row B placeholder".to_string(),
    };
    let mut precise_a = native_a.clone();
    precise_a.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::i128(), trust_types::Ty::i128()),
    };
    let mut precise_b = native_b.clone();
    precise_b.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Mul,
        operand_tys: (trust_types::Ty::i128(), trust_types::Ty::i128()),
    };
    let results = vec![
        (native_a.clone(), authority_test_proved()),
        (native_b.clone(), authority_test_proved()),
    ];
    let obligation_a = authority_test_native_obligation("bridge:stale-reseal:A", 37, 37);
    let obligation_b = authority_test_native_obligation("bridge:stale-reseal:B", 38, 38);
    let binding_a = test_binding_for_obligation(0, &native_a, &obligation_a);
    let binding_b = test_binding_for_obligation(1, &native_b, &obligation_b);
    let mut swapped = vec![binding_b, binding_a];
    let before_bindings = swapped.clone();

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        &[precise_a, precise_b],
        &mut swapped,
        results.clone(),
    );

    assert_eq!((proved, failed), (0, 0));
    assert_eq!(bridged.len(), results.len());
    assert!(
        bridged.iter().zip(&results).all(|((actual_vc, actual), (expected_vc, expected))| {
            exact_vc_key(actual_vc) == exact_vc_key(expected_vc)
                && matches!(actual, VerificationResult::Proved { .. })
                && matches!(expected, VerificationResult::Proved { .. })
        }),
        "stale bindings must not re-key either result row"
    );
    assert_eq!(
        swapped, before_bindings,
        "the semantic replacement path must not self-repair a swapped binding"
    );
}

fn bridge_test_unknown() -> VerificationResult {
    VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "native proof candidate was not authoritative".to_string(),
    }
}

#[test]
fn v1_bridge_disambiguates_distinct_exact_vcs_at_one_source_span() {
    let mut initiation = test_vc(39);
    let initiation_atom = Formula::Var("initiation_holds".to_string(), Sort::Bool);
    initiation.formula =
        Formula::And(vec![initiation_atom.clone(), Formula::Not(Box::new(initiation_atom))]);
    let mut consecution = test_vc(39);
    let consecution_atom = Formula::Var("consecution_holds".to_string(), Sort::Bool);
    consecution.formula =
        Formula::And(vec![consecution_atom.clone(), Formula::Not(Box::new(consecution_atom))]);
    assert!(exact_vc_key(&initiation) != exact_vc_key(&consecution));

    let obligation_a = authority_test_native_obligation("bridge:exact-same-span:A", 39, 39);
    let obligation_b = authority_test_native_obligation("bridge:exact-same-span:B", 39, 39);
    let mut bindings = vec![
        test_binding_for_obligation(0, &initiation, &obligation_a),
        test_binding_for_obligation(1, &consecution, &obligation_b),
    ];
    let solver_vcs = vec![initiation.clone(), consecution.clone()];
    let results = vec![
        (initiation.clone(), bridge_test_unknown()),
        (consecution.clone(), bridge_test_unknown()),
    ];

    let (bridged, proved, failed, _) =
        bridge_v1_ay_proofs_into_native_results(5_000, None, &solver_vcs, &mut bindings, results);

    assert_eq!((proved, failed), (2, 0));
    assert!(bridged.iter().all(|(_, result)| matches!(result, VerificationResult::Proved { .. })));
    for (index, (vc, _)) in bridged.iter().enumerate() {
        assert!(exact_vc_key(vc) == exact_vc_key(&solver_vcs[index]));
        assert!(bindings[index].as_ref().is_some_and(|binding| binding.matches_row(index, vc)));
    }
}

#[test]
fn v1_bridge_rejects_duplicate_exact_vcs_even_with_valid_row_bindings() {
    let mut vc = test_vc(40);
    let atom = Formula::Var("duplicate_exact".to_string(), Sort::Bool);
    vc.formula = Formula::And(vec![atom.clone(), Formula::Not(Box::new(atom))]);
    let obligation_a = authority_test_native_obligation("bridge:duplicate-exact:A", 40, 40);
    let obligation_b = authority_test_native_obligation("bridge:duplicate-exact:B", 40, 40);
    let mut bindings = vec![
        test_binding_for_obligation(0, &vc, &obligation_a),
        test_binding_for_obligation(1, &vc, &obligation_b),
    ];

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        &[vc.clone(), vc.clone()],
        &mut bindings,
        vec![(vc.clone(), bridge_test_unknown()), (vc.clone(), bridge_test_unknown())],
    );

    assert_eq!((proved, failed), (0, 0));
    assert!(bridged.iter().all(|(_, result)| matches!(result, VerificationResult::Unknown { .. })));
}

#[test]
fn v1_bridge_rejects_duplicate_exact_solver_carrier_only() {
    let mut vc = test_vc(401);
    let atom = Formula::Var("duplicate_solver_only".to_string(), Sort::Bool);
    vc.formula = Formula::And(vec![atom.clone(), Formula::Not(Box::new(atom))]);
    let obligation = authority_test_native_obligation("bridge:duplicate-solver-only", 401, 401);
    let mut bindings = vec![test_binding_for_obligation(0, &vc, &obligation)];

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        &[vc.clone(), vc.clone()],
        &mut bindings,
        vec![(vc, bridge_test_unknown())],
    );

    assert_eq!((proved, failed), (0, 0));
    assert!(matches!(bridged[0].1, VerificationResult::Unknown { .. }));
}

#[test]
fn v1_bridge_rejects_duplicate_exact_result_carrier_only() {
    let mut vc = test_vc(402);
    let atom = Formula::Var("duplicate_result_only".to_string(), Sort::Bool);
    vc.formula = Formula::And(vec![atom.clone(), Formula::Not(Box::new(atom))]);
    let obligation_a = authority_test_native_obligation("bridge:duplicate-result-only:A", 402, 402);
    let obligation_b = authority_test_native_obligation("bridge:duplicate-result-only:B", 403, 402);
    let mut bindings = vec![
        test_binding_for_obligation(0, &vc, &obligation_a),
        test_binding_for_obligation(1, &vc, &obligation_b),
    ];

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        std::slice::from_ref(&vc),
        &mut bindings,
        vec![(vc.clone(), bridge_test_unknown()), (vc.clone(), bridge_test_unknown())],
    );

    assert_eq!((proved, failed), (0, 0));
    assert!(bridged.iter().all(|(_, result)| matches!(result, VerificationResult::Unknown { .. })));
}

#[test]
fn v1_bridge_does_not_solve_unsupported_capability_sentinels() {
    let mut unsupported = test_vc(41);
    unsupported.kind = VcKind::UnsupportedMir {
        kind: "UserLoopContractUnsupported".to_string(),
        detail: "invariant references unsupported or ambiguous MIR value".to_string(),
    };
    unsupported.formula = Formula::Bool(true);
    let obligation = authority_test_native_obligation("bridge:unsupported-sentinel", 41, 41);
    let mut bindings = vec![test_binding_for_obligation(0, &unsupported, &obligation)];

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        std::slice::from_ref(&unsupported),
        &mut bindings,
        vec![(unsupported.clone(), bridge_test_unknown())],
    );

    assert_eq!((proved, failed), (0, 0));
    assert!(matches!(bridged[0].1, VerificationResult::Unknown { .. }));
}

#[test]
fn v1_bridge_rejects_ambiguous_same_span_arithmetic_fallback() {
    let mut native_placeholder = test_vc(35);
    native_placeholder.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "native arithmetic obligation lacks a unique legacy identity".to_string(),
    };
    native_placeholder.formula = trust_types::Formula::Bool(false);
    let native_unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "native arithmetic safety was unsupported".to_string(),
    };

    let mut add_overflow = test_vc(35);
    add_overflow.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::i128(), trust_types::Ty::i128()),
    };
    let atom = trust_types::Formula::Var("add_overflow".to_string(), trust_types::Sort::Bool);
    add_overflow.formula =
        trust_types::Formula::And(vec![atom.clone(), trust_types::Formula::Not(Box::new(atom))]);

    let mut mul_overflow = test_vc(35);
    mul_overflow.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Mul,
        operand_tys: (trust_types::Ty::i128(), trust_types::Ty::i128()),
    };
    mul_overflow.formula = trust_types::Formula::Bool(true);
    let obligation = authority_test_native_obligation("bridge:ambiguous", 35, 35);
    let mut bindings = vec![test_binding_for_obligation(0, &native_placeholder, &obligation)];

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        &[add_overflow, mul_overflow],
        &mut bindings,
        vec![(native_placeholder.clone(), native_unknown)],
    );

    assert_eq!((proved, failed), (0, 0));
    assert!(matches!(bridged[0].1, VerificationResult::Unknown { .. }));
    assert!(
        exact_vc_key(&bridged[0].0) == exact_vc_key(&native_placeholder),
        "a source span shared by multiple VCs must fail closed instead of borrowing either verdict"
    );
}

#[test]
fn v1_bridge_rejects_unique_same_span_with_different_formula() {
    let mut native = test_vc(36);
    native.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::ArithmeticSafety".to_string(),
        detail: "native row and v1 row share presentation coordinates only".to_string(),
    };
    native.formula =
        trust_types::Formula::Var("native_violation".to_string(), trust_types::Sort::Bool);
    let native_unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "unsupported".to_string(),
    };

    let mut neighboring = test_vc(36);
    neighboring.kind = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::i128(), trust_types::Ty::i128()),
    };
    let atom = trust_types::Formula::Var("neighbor_violation".to_string(), trust_types::Sort::Bool);
    neighboring.formula =
        trust_types::Formula::And(vec![atom.clone(), trust_types::Formula::Not(Box::new(atom))]);
    let obligation = authority_test_native_obligation("bridge:mismatch", 36, 36);
    let mut bindings = vec![test_binding_for_obligation(0, &native, &obligation)];

    let (bridged, proved, failed, _) = bridge_v1_ay_proofs_into_native_results(
        5_000,
        None,
        std::slice::from_ref(&neighboring),
        &mut bindings,
        vec![(native.clone(), native_unknown)],
    );

    assert_eq!((proved, failed), (0, 0));
    assert!(matches!(bridged[0].1, VerificationResult::Unknown { .. }));
    assert_eq!(bridged[0].0.formula, native.formula);
}

// Trust (#47/#48): a known-panicking unsupported call that was somehow PROVED (e.g. a
// future model that establishes panic-freedom) must NOT be counted as failed — the
// reclassification only fires on a non-`Proved` verdict.
#[test]
fn strict_l0_verification_does_not_refute_proved_known_panicking_call() {
    let mut unwrap_vc = test_vc(23);
    unwrap_vc.kind = VcKind::UnsupportedMir {
        kind: "Call::unwrap::panic-freedom-unverified".to_string(),
        detail: "bb0: `unwrap` panics on None/Err".to_string(),
    };
    let proved = VerificationResult::Proved {
        solver: trust_types::Symbol::intern("ay"),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    // Not full-verifier-backed (None), Proved + no runtime fallback for UnsupportedMir →
    // counted `unknown`, NOT `failed`. The key assertion is `failed == 0`.
    assert_eq!(
        strict_l0_verification_failure(true, &[(unwrap_vc, proved)], &[], &[], None),
        Some(FullVerificationFailure { failed: 0, unknown: 1, runtime_checked: 0, skipped: 0 }),
    );
}

#[test]
fn strict_l0_verification_rejects_public_l0_api_obligations_not_compiler_proved() {
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "obl-memory".to_string(),
        kind: trust_verifier_api::ObligationKind::MemorySafety,
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "memory safety".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-memory",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::f".to_string(),
        },
    );
    bundle.obligations.push(obligation.clone());
    let evidence = trust_verifier_api::ObligationEvidence {
        evidence_id: "trust-vc:memory".to_string(),
        obligation_id: obligation.obligation_id.clone(),
        engine: trust_verifier_api::EngineManifest::new(
            "trust-vc",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Deductive,
        ),
        status: trust_verifier_api::EvidenceStatus::Proved,
        proof_strength: None,
        artifacts: Vec::new(),
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: Vec::new(),
    };
    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("strict-l0-test").snapshot(),
        &bundle,
        evidence.engine.clone(),
        &[obligation],
        vec![evidence],
    );

    assert_eq!(
        strict_l0_verification_failure(true, &[], &[], &[], Some(&full_result)),
        Some(FullVerificationFailure { failed: 0, unknown: 1, runtime_checked: 0, skipped: 0 }),
    );
}

// Trust (assumption ledger): reporting-role metadata never weakens the
// abort-vs-record matrix. Batteries-on verification rejects capability gaps;
// only the explicit survey policy makes them nonfatal.
#[test]
fn assumption_ledger_skip_abort_matrix() {
    use trust_mir_extract::supportability::UnsupportedReason;

    let assumption = TrustVerifySkipReason::TreatedAsAssumption(UnsupportedReason::PatternType);

    let strict_policy = test_policy(false, false);
    assert!(strict_policy.skip_aborts_build(&assumption));
    assert!(strict_policy.skip_aborts_build(&TrustVerifySkipReason::UnreachableStart));
    assert!(strict_policy.skip_aborts_build(&TrustVerifySkipReason::UserOptOut));

    // `ContractGeneratedClosure` never aborts. It
    // joined this set in the P0 "stop false-refuting dead contract-checker closures"
    // fix: inherited checker closures are not part of Trust's canonical proof
    // inventory, so their absence is never-a-gap
    // (`skip_is_full_verification_failure` returns false).
    assert!(!strict_policy.skip_aborts_build(&TrustVerifySkipReason::ContractGeneratedClosure));

    // Survey preserves evidence routing but never aborts.
    let survey_policy = test_policy(true, false);
    assert!(survey_policy.is_explicit_advisory());
    assert!(!survey_policy.fail_closed());
    assert!(!survey_policy.skip_aborts_build(&assumption));
}

#[test]
fn explicit_invalid_solver_path_fails_closed_without_sibling_fallback() {
    let executable = std::env::current_exe().expect("current test executable");
    let missing = executable.with_file_name("trust-missing-ay-solver");
    let _ = std::fs::remove_file(&missing);

    let identity = resolve_ay_solver_identity_from_candidates(
        Some(missing.as_os_str().to_os_string()),
        Some(executable),
    );
    assert_eq!(identity.path.as_deref(), Some(missing.as_path()));
    assert_eq!(identity.availability, AySolverAvailability::NotExecutable);
    assert!(identity.router_command().is_none());
    assert!(identity.cache_fingerprint().is_none());
}

#[test]
fn solver_identity_reuses_one_exact_path_and_content_key() {
    let executable = std::env::current_exe().expect("current test executable");
    let identity = resolve_ay_solver_identity_from_candidates(
        Some(executable.as_os_str().to_os_string()),
        Some(executable.with_file_name("must-not-be-selected")),
    );
    let fingerprint = identity.cache_fingerprint().expect("test executable is readable");

    assert_eq!(identity.path.as_deref(), Some(executable.as_path()));
    let snapshot = identity.snapshot_path.as_deref().expect("Session snapshot");
    assert_ne!(snapshot, executable, "the router must not execute the mutable source path");
    assert_eq!(identity.router_command(), snapshot.to_str());
    assert!(snapshot.is_file());
    assert_eq!(identity.availability, AySolverAvailability::Available);
    assert_eq!(identity.semantics_key(), format!("ay:{fingerprint}"));
    assert_eq!(
        identity.binary_fingerprint.as_ref().unwrap().content_digest().len(),
        64,
        "the immutable identity carries a strong full-content digest"
    );
}

#[cfg(unix)]
#[test]
fn non_unicode_solver_path_never_fabricates_a_lossy_router_command() {
    use std::os::unix::ffi::{OsStrExt, OsStringExt};
    use std::os::unix::fs::PermissionsExt;

    let mut bytes = std::env::temp_dir().as_os_str().as_bytes().to_vec();
    bytes.extend_from_slice(format!("/trust-ay-nonunicode-{}-", std::process::id()).as_bytes());
    bytes.push(0xff);
    let path = PathBuf::from(OsString::from_vec(bytes));
    let _ = std::fs::remove_file(&path);
    assert!(path.to_str().is_none(), "test setup: path is not Unicode");
    assert!(
        exact_solver_command(&path).is_none(),
        "the router's String API must never receive a lossy replacement path"
    );
    if let Err(error) = std::fs::write(&path, b"#!/bin/sh\nexit 0\n") {
        // Darwin/APFS rejects ill-formed UTF-8 path components (EILSEQ), so the
        // pure exact-conversion assertion above is the available regression on
        // that platform. Filesystems that accept arbitrary Unix bytes exercise
        // the complete snapshot path below.
        #[cfg(target_os = "macos")]
        {
            assert_eq!(error.raw_os_error(), Some(92), "unexpected path creation error: {error}");
            return;
        }
        #[cfg(not(target_os = "macos"))]
        panic!("unexpected path creation error: {error}");
    }
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))
        .expect("make solver executable");
    let identity =
        resolve_ay_solver_identity_from_candidates(Some(path.as_os_str().to_os_string()), None);
    let _ = std::fs::remove_file(&path);

    assert_eq!(identity.path.as_deref(), Some(path.as_path()));
    assert_eq!(identity.availability, AySolverAvailability::Available);
    assert!(
        identity.router_command().is_some_and(|command| !command.contains('\u{fffd}')),
        "the router must execute an exact private snapshot, never a lossy source path"
    );
}

#[cfg(unix)]
#[test]
fn solver_execution_snapshot_cannot_drift_after_identity_is_hashed() {
    use std::os::unix::fs::PermissionsExt;

    let source =
        std::env::temp_dir().join(format!("trust-ay-toctou-source-{}", std::process::id()));
    let old_bytes = b"#!/bin/sh\nexit 7\n";
    let new_bytes = b"#!/bin/sh\nexit 9\n";
    std::fs::write(&source, old_bytes).expect("write solver");
    std::fs::set_permissions(&source, std::fs::Permissions::from_mode(0o700))
        .expect("make solver executable");

    let identity =
        resolve_ay_solver_identity_from_candidates(Some(source.as_os_str().to_os_string()), None);
    let snapshot = identity.snapshot_path.as_ref().expect("snapshot").clone();
    let original_key = identity.cache_fingerprint().expect("fingerprint").to_string();
    std::fs::write(&source, new_bytes).expect("replace selected solver bytes");

    assert_eq!(std::fs::read(&snapshot).unwrap(), old_bytes);
    assert_ne!(std::fs::read(&source).unwrap(), std::fs::read(&snapshot).unwrap());
    assert_eq!(
        trust_cache::fingerprint_solver_binary("ay", &snapshot).unwrap().cache_key(),
        original_key,
        "the cache key must identify the exact path the router will execute"
    );
    assert_eq!(identity.router_command(), snapshot.to_str());

    let _ = std::fs::remove_file(source);
}

#[cfg(unix)]
#[test]
fn same_solver_path_with_different_bytes_changes_the_crate_hash_input() {
    use std::os::unix::fs::PermissionsExt;

    let source =
        std::env::temp_dir().join(format!("trust-ay-replaced-in-place-{}", std::process::id()));
    std::fs::write(&source, b"#!/bin/sh\nexit 7\n").expect("write first solver");
    std::fs::set_permissions(&source, std::fs::Permissions::from_mode(0o700))
        .expect("make solver executable");
    let first =
        resolve_ay_solver_identity_from_candidates(Some(source.as_os_str().to_os_string()), None);

    std::fs::write(&source, b"#!/bin/sh\nexit 9\n").expect("replace solver at same path");
    let second =
        resolve_ay_solver_identity_from_candidates(Some(source.as_os_str().to_os_string()), None);
    let _ = std::fs::remove_file(&source);

    assert_eq!(first.path, second.path, "test must keep the configured path identical");
    assert_ne!(first.semantics_key(), second.semantics_key());

    let mut first_opts = rustc_session::config::Options::default();
    first_opts.unstable_opts.trust_verify_ay_path = Some(source.clone());
    first_opts.trust_solver_content_fingerprint = first.semantics_key();
    let mut second_opts = first_opts.clone();
    second_opts.trust_solver_content_fingerprint = second.semantics_key();
    assert_ne!(
        first_opts.dep_tracking_hash(true),
        second_opts.dep_tracking_hash(true),
        "same path plus replaced solver bytes must rotate the downstream crate hash"
    );
}

#[cfg(unix)]
#[test]
fn moved_identical_solver_bytes_keep_the_same_semantics_and_cache_key() {
    use std::os::unix::fs::PermissionsExt;

    let base = std::env::temp_dir();
    let path_a = base.join(format!("trust-ay-moved-a-{}", std::process::id()));
    let path_b = base.join(format!("trust-ay-moved-b-{}", std::process::id()));
    let bytes = b"#!/bin/sh\nexit 0\n";
    for path in [&path_a, &path_b] {
        std::fs::write(path, bytes).expect("write solver copy");
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700))
            .expect("make solver executable");
    }
    let a =
        resolve_ay_solver_identity_from_candidates(Some(path_a.as_os_str().to_os_string()), None);
    let b =
        resolve_ay_solver_identity_from_candidates(Some(path_b.as_os_str().to_os_string()), None);
    let _ = std::fs::remove_file(&path_a);
    let _ = std::fs::remove_file(&path_b);

    assert_ne!(a.path, b.path);
    assert_eq!(a.cache_fingerprint(), b.cache_fingerprint());
    assert_eq!(a.semantics_key(), b.semantics_key());

    let mut opts_a = rustc_session::config::Options::default();
    opts_a.unstable_opts.trust_verify_ay_path = Some(path_a);
    opts_a.trust_solver_content_fingerprint = a.semantics_key();
    let mut opts_b = opts_a.clone();
    opts_b.unstable_opts.trust_verify_ay_path = Some(path_b);
    opts_b.trust_solver_content_fingerprint = b.semantics_key();
    assert_eq!(
        opts_a.dep_tracking_hash(true),
        opts_b.dep_tracking_hash(true),
        "moving byte-identical solver contents must not invalidate downstream crates"
    );
}

// Trust (assumption ledger, Stage 1): the ledger tags are a stable
// machine-readable registry — ascii lowercase + dashes, pinned values.
#[test]
fn assumption_ledger_tags_are_stable() {
    use trust_mir_extract::supportability::UnsupportedReason;

    assert_eq!(skip_assumption_tag(&TrustVerifySkipReason::UnreachableStart), "unreachable-start");
    assert_eq!(skip_assumption_tag(&TrustVerifySkipReason::UserOptOut), "user-opt-out");
    // Delegation to UnsupportedReason::tag() (its own stability test pins the
    // full registry; spot-check the reachable-from-classify values here).
    for (reason, tag) in [
        (UnsupportedReason::Coroutine, "coroutine"),
        (UnsupportedReason::PatternType, "pattern-type"),
        (UnsupportedReason::AddressOfField, "addr-of-field"),
        (UnsupportedReason::ThreadLocalRef, "thread-local-ref"),
        (UnsupportedReason::EscapedBinderOrInferVar, "escaped-binder"),
    ] {
        let got = skip_assumption_tag(&TrustVerifySkipReason::TreatedAsAssumption(reason));
        assert_eq!(got, tag);
        assert!(
            got.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-'),
            "tag charset must stay machine-stable: {got}"
        );
    }
    // Capability gaps and explicit user opt-outs are recorded assumptions.
    assert!(skip_reason_is_recorded_assumption(&TrustVerifySkipReason::UnreachableStart));
    assert!(skip_reason_is_recorded_assumption(&TrustVerifySkipReason::TreatedAsAssumption(
        UnsupportedReason::Coroutine
    )));
    assert!(skip_reason_is_recorded_assumption(&TrustVerifySkipReason::UserOptOut));
    assert!(!skip_reason_is_recorded_assumption(&TrustVerifySkipReason::ExternalDependencyScope));
    assert!(!skip_reason_is_recorded_assumption(&TrustVerifySkipReason::NonLocalMir));
}

// ---------------------------------------------------------------------------
// Trust (hardened evidence gate): exact row identity + bridge-lane evidence
// ---------------------------------------------------------------------------

/// A sep-engine unsafe VC exactly as `trust_vcgen::sep_engine` emits it: an
/// `Assertion` whose message carries the `[unsafe:sep:..]` marker, with a real
/// (non-tautology) violation formula.
fn unsafe_sep_assertion_vc(function: &str) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "[unsafe:sep:alloc] allocation result null check for _3 in {function}"
            ),
        },
        function: trust_types::Symbol::intern(function),
        location: native_trust_ir_test_span(21),
        formula: trust_types::Formula::Eq(
            Box::new(trust_types::Formula::Var("ptr_0".to_string(), trust_types::Sort::Int)),
            Box::new(trust_types::Formula::Int(0)),
        ),
        contract_metadata: None,
    }
}

fn bridge_test_solver_revalidated_authorities(
    results: &[(VerificationCondition, VerificationResult)],
    bindings: &[Option<ResultObligationBinding>],
) -> Vec<Option<ResultProofAuthority>> {
    results
        .iter()
        .enumerate()
        .map(|(index, (vc, result))| {
            let VerificationResult::Proved { solver, .. } = result else {
                return None;
            };
            if solver.as_str() != "ay-in-process"
                || !bindings
                    .get(index)
                    .and_then(Option::as_ref)
                    .is_some_and(|binding| binding.matches_row(index, vc))
            {
                return None;
            }
            let row = exact_result_row_identity(index, vc)?;
            let canonical_problem = trust_router::in_process_ay_backend::problem_smt2(&vc.formula);
            let receipt = SolverRevalidationReceipt {
                row_index: index,
                canonical_vc: row.canonical_vc.clone(),
                problem_sha256: trust_types::stable_sha256_hex(canonical_problem.as_bytes()),
                canonical_problem,
                time_ms: 1,
            };
            Some(ResultProofAuthority::SolverRevalidated { row, receipt })
        })
        .collect()
}

#[test]
fn solver_revalidation_authority_rechecks_its_complete_receipt() {
    let vc = unsafe_sep_assertion_vc("crate::receipt_target");
    let row = exact_result_row_identity(0, &vc).expect("canonical row");
    let canonical_problem = trust_router::in_process_ay_backend::problem_smt2(&vc.formula);
    let mut authority = ResultProofAuthority::SolverRevalidated {
        row: row.clone(),
        receipt: SolverRevalidationReceipt {
            row_index: 0,
            canonical_vc: row.canonical_vc,
            problem_sha256: trust_types::stable_sha256_hex(canonical_problem.as_bytes()),
            canonical_problem,
            time_ms: 1,
        },
    };
    assert!(authority.matches_row(0, &vc, None));
    let ResultProofAuthority::SolverRevalidated { receipt, .. } = &mut authority else {
        unreachable!()
    };
    receipt.canonical_problem.push_str("\n; substituted after mint");
    assert!(
        !authority.matches_row(0, &vc, None),
        "a stale or substituted replay receipt must lose exact-row authority",
    );

    let empty_citation = ResultProofAuthority::EnsuresCitationDischarge {
        row: exact_result_row_identity(0, &vc).expect("canonical row"),
        theorem: String::new(),
    };
    assert!(
        !empty_citation.matches_row(0, &vc, None),
        "an empty theorem provenance carrier must not retain citation authority",
    );
}

#[test]
fn hardened_sep_assertion_retains_exact_requested_obligation_identity() {
    let (function, compiler_contracts, _) = native_trust_ir_compiler_function();
    let vc = unsafe_sep_assertion_vc(&function.def_path);
    let bundle = trust_mir_extract::function_to_verifier_api_bundle(
        &function,
        &compiler_contracts,
        std::slice::from_ref(&vc),
    );
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation.metadata.iter().any(|entry| entry.key == "trust.vc.hardened.category")
        })
        .expect("a [unsafe:sep] Assertion VC must produce a hardened obligation");

    let binding = test_binding_for_obligation(0, &vc, obligation).expect("binding");
    assert_eq!(binding.public_obligation_id, obligation.obligation_id);
    assert_eq!(binding.native_identity, native_transport_identity(obligation));
}

#[test]
fn bridge_lane_appends_publishable_obligation_evidence_for_ay_proofs() {
    let (function, compiler_contracts, mut vcs) = native_trust_ir_compiler_function();
    let sep_vc = unsafe_sep_assertion_vc(&function.def_path);
    vcs.push(sep_vc.clone());
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("hardened + arithmetic obligations require native TrustIr");
    let mut full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("bridge-evidence-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "test-composite",
            "test",
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        Vec::new(),
    );

    let lrat = b"p lrat test certificate".to_vec();
    let results = vec![(
        sep_vc.clone(),
        VerificationResult::Proved {
            solver: trust_types::Symbol::intern("ay-in-process"),
            time_ms: 1,
            strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(lrat.clone()),
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let sep_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation.metadata.iter().any(|entry| entry.key == "trust.vc.hardened.category")
        })
        .expect("hardened obligation");
    let result_bindings = vec![test_binding_for_obligation(0, &results[0].0, sep_obligation)];
    let proof_authorities = bridge_test_solver_revalidated_authorities(&results, &result_bindings);
    assert!(
        full_result
            .skipped
            .iter()
            .any(|skipped| skipped.obligation_id == sep_obligation.obligation_id)
    );
    let mut duplicate_skip_result = full_result.clone();
    let duplicate_skip = duplicate_skip_result
        .skipped
        .iter()
        .find(|skipped| skipped.obligation_id == sep_obligation.obligation_id)
        .expect("bridge fixture skip")
        .clone();
    duplicate_skip_result.skipped.push(duplicate_skip);
    let malformed_before = duplicate_skip_result.clone();
    let malformed_error = append_bridge_lane_full_verification_evidence(
        &mut duplicate_skip_result,
        Some(&native_trust_ir_bundle),
        &results,
        &result_bindings,
        &proof_authorities,
    )
    .expect_err("a malformed source carrier must fail before bridge mutation");
    assert!(
        malformed_error.contains("skipped obligations"),
        "unexpected malformed-carrier rejection: {malformed_error}",
    );
    assert_eq!(
        duplicate_skip_result, malformed_before,
        "malformed source rejection must be byte-for-byte transactional"
    );
    assert!(
        !duplicate_skip_result
            .evidence
            .iter()
            .any(|evidence| evidence.evidence_id.starts_with("bridge-ay:")),
        "duplicate typed skips are ambiguous and must reject bridge publication"
    );
    let pre_bridge_run = full_result.clone();
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut full_result,
            Some(&native_trust_ir_bundle),
            &results,
            &result_bindings,
            &proof_authorities,
        ),
        Ok(true),
    );
    assert!(
        is_permitted_bridge_publication_transition(&pre_bridge_run, &full_result),
        "the exact transactional AY replacement must be accepted as the sole source-to-final delta",
    );
    full_result
        .validate_derived_state()
        .expect("bridge evidence replacement must leave a canonical public run");
    full_result
        .try_to_manifest()
        .expect("bridge evidence replacement must remain losslessly manifestable");

    let evidence = full_result
        .evidence
        .iter()
        .find(|evidence| evidence.evidence_id.starts_with("bridge-ay:"))
        .expect("bridge lane must append evidence for the ay-proved hardened obligation");
    assert_eq!(evidence.status, trust_verifier_api::EvidenceStatus::Proved);
    assert_eq!(
        evidence.engine, full_result.engine,
        "accepted child evidence must retain the composite publication envelope; ay provenance lives in the evidence DAG and diagnostics"
    );
    assert!(
        evidence
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.contains("primary owner ay-in-process@bridge-v1") })
    );
    assert!(
        evidence
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("supersedes native skipped row"))
    );
    assert!(
        !full_result
            .skipped
            .iter()
            .any(|skipped| skipped.obligation_id == sep_obligation.obligation_id),
        "a strict bridge proof and a typed skip for the same row are contradictory"
    );
    assert!(
        build_full_verification_evidence_index(&full_result)
            .strict_accepted_by_obligation_id
            .contains_key(sep_obligation.obligation_id.as_str()),
        "composite-wrapped bridge evidence must enter the strict compiler index"
    );
    assert!(
        evidence.is_unbounded_proof(),
        "bridge evidence must satisfy the publication-grade strength + artifact policy"
    );

    assert!(!evidence.artifacts.iter().any(|artifact| {
        artifact.kind == trust_verifier_api::EvidenceArtifactKind::ProofCertificate
    }));
    let input = evidence
        .artifacts
        .iter()
        .find(|artifact| artifact.uri.starts_with("trust-bridge://ay-in-process/normalized-input/"))
        .expect("bridge evidence must carry its exact normalized solver input");
    let transcript = evidence
        .artifacts
        .iter()
        .find(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::SolverTranscript
        })
        .expect("bridge evidence must carry exact retained LRAT bytes");
    let check = evidence
        .artifacts
        .iter()
        .find(|artifact| {
            artifact.kind == trust_verifier_api::EvidenceArtifactKind::ProofCheckReport
        })
        .expect("bridge evidence must carry the strict checker result");
    let input_materialization =
        input.materialization.as_ref().expect("normalized input must be materialized");
    let transcript_materialization =
        transcript.materialization.as_ref().expect("LRAT transcript must be materialized");
    let check_materialization =
        check.materialization.as_ref().expect("strict check report must be materialized");
    assert_eq!(
        input_materialization.bound_payload_bytes(input.kind, &evidence.obligation_id),
        Some(trust_router::in_process_ay_backend::problem_smt2(&sep_vc.formula).as_bytes()),
    );
    assert_eq!(
        transcript_materialization.bound_payload_bytes(transcript.kind, &evidence.obligation_id),
        Some(lrat.as_slice()),
    );
    assert_eq!(
        transcript_materialization.referenced_artifacts(),
        [trust_verifier_api::EvidenceArtifactReference {
            kind: input.kind,
            hash: input.hash.clone(),
        }],
    );
    assert_eq!(
        check_materialization.referenced_artifacts(),
        [trust_verifier_api::EvidenceArtifactReference {
            kind: transcript.kind,
            hash: transcript.hash.clone(),
        }],
    );
    let check_payload = check_materialization
        .bound_payload_bytes(check.kind, &evidence.obligation_id)
        .expect("strict check payload");
    let check_json: serde_json::Value =
        serde_json::from_slice(check_payload).expect("strict check JSON");
    assert_eq!(check_json["strict_verdict"], "verified");
    assert_eq!(check_json["acceptance_mode"], "strict");
    assert_eq!(check_json["lrat_payload_sha256"], trust_types::stable_sha256_hex(&lrat));
    let mut owner_transplant = evidence.clone();
    owner_transplant.obligation_id = "vc:attacker::transplanted:0".to_string();
    assert!(
        !owner_transplant.is_unbounded_proof(),
        "an exact proof DAG must not survive an obligation-owner transplant"
    );

    // The typed native-TrustIr binding triple (bundle / request / proof) must
    // be attached, recomputed from the held bundle.
    assert_eq!(
        evidence
            .artifacts
            .iter()
            .filter(|artifact| artifact.uri.starts_with("trust_ir-native://"))
            .count(),
        3,
    );

    // And the appended evidence binds to the obligation whose native identity
    // metadata is declared on the bundle side.
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == evidence.obligation_id)
        .expect("appended evidence must reference a requested obligation");
    let identity = native_transport_identity(obligation);
    assert!(identity.suite.is_some());
    assert!(identity.request_id.is_some());
    assert!(identity.native_id.is_some());
    for materialization in
        [input_materialization, transcript_materialization, check_materialization]
    {
        assert_eq!(materialization.proof_binding_id(), identity.native_id.as_deref().unwrap());
    }
}

#[test]
fn bridge_publication_stays_non_proved_when_injected_s1_revalidation_misses() {
    let (function, compiler_contracts, mut vcs) = native_trust_ir_compiler_function();
    let sep_vc = unsafe_sep_assertion_vc(&function.def_path);
    vcs.push(sep_vc.clone());
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("S1 publication fixture requires native TrustIr");
    let mut full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("bridge-s1-miss-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "test-composite",
            "test",
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        Vec::new(),
    );
    let sep_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation.metadata.iter().any(|entry| entry.key == "trust.vc.hardened.category")
        })
        .expect("hardened obligation");
    let results = vec![(
        sep_vc,
        VerificationResult::Proved {
            solver: trust_types::Symbol::intern("ay-in-process"),
            time_ms: 1,
            strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(b"p lrat producer proof".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let bindings = vec![test_binding_for_obligation(0, &results[0].0, sep_obligation)];
    let row = exact_result_row_identity(0, &results[0].0).expect("exact S1 row");
    let expected_problem = trust_router::in_process_ay_backend::problem_smt2(&results[0].0.formula);
    let eligibilities = vec![Some(SolverRevalidationEligibility {
        row,
        producer_canonical_problem: expected_problem,
    })];
    let cleancic = vec![None];
    let mut attempts = 0;
    let revalidations = revalidate_all_solver_proofs_with(
        &results,
        &eligibilities,
        &cleancic,
        None,
        std::time::Instant::now,
        |_formula, _budget_ms| {
            attempts += 1;
            None
        },
    );
    assert_eq!(attempts, 1, "fixture must reach the injected fresh replay");
    assert!(revalidations.iter().all(Option::is_none));
    let authorities = build_result_proof_authorities_with_revalidations(
        &results,
        &bindings,
        Some(&full_result),
        &cleancic,
        &revalidations,
    );
    assert!(authorities.iter().all(Option::is_none));

    let before = full_result.clone();
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut full_result,
            Some(&native_trust_ir_bundle),
            &results,
            &bindings,
            &authorities,
        ),
        Ok(false),
    );
    assert_eq!(full_result, before, "an S1 miss must leave the canonical public run unchanged");
    assert_eq!(full_result.summary.proved, 0);
    assert_ne!(full_result.status, trust_verifier_api::VerificationRunStatus::Proved);
    assert!(!full_result.evidence.iter().any(|evidence| {
        evidence.obligation_id == sep_obligation.obligation_id
            && evidence.status == trust_verifier_api::EvidenceStatus::Proved
    }));
    full_result.validate_derived_state().expect("unchanged S1-miss run remains canonical");
}

#[test]
fn bridge_evidence_rejects_two_valid_bindings_swapped_between_rows() {
    let (function, compiler_contracts, mut vcs) = native_trust_ir_compiler_function();
    vcs.push(unsafe_sep_assertion_vc(&function.def_path));
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("bridge swap fixture requires native TrustIr");
    let binding_index = trust_router::full_verification::NativeTrustIrBindingIndex::from_bundle(
        &native_trust_ir_bundle,
    );
    let obligations = bundle
        .obligations
        .iter()
        .filter(|obligation| {
            native_identity_is_complete_and_canonical(&native_transport_identity(obligation))
                && matches!(binding_index.binding_artifacts_for_obligation(obligation), Ok(Some(_)))
        })
        .take(2)
        .collect::<Vec<_>>();
    assert_eq!(obligations.len(), 2, "fixture needs two backed native proof units");

    let results = obligations
        .iter()
        .enumerate()
        .map(|(index, obligation)| {
            (
                legacy_vc_from_api_obligation(&function, obligation),
                VerificationResult::Proved {
                    solver: trust_types::Symbol::intern("ay-in-process"),
                    time_ms: 1,
                    strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
                    proof_certificate: Some(format!("p lrat row {index}").into_bytes()),
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            )
        })
        .collect::<Vec<_>>();
    let bindings = obligations
        .iter()
        .enumerate()
        .map(|(index, obligation)| {
            test_binding_for_obligation(index, &results[index].0, obligation)
        })
        .collect::<Vec<_>>();
    let proof_authorities = bridge_test_solver_revalidated_authorities(&results, &bindings);
    assert!(bindings.iter().enumerate().all(|(index, binding)| {
        binding.as_ref().is_some_and(|binding| binding.matches_row(index, &results[index].0))
    }));

    let mut full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("bridge-row-seal-swap-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "test-composite",
            "test",
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        Vec::new(),
    );
    let mut correct = full_result.clone();
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut correct,
            Some(&native_trust_ir_bundle),
            &results,
            &bindings,
            &proof_authorities,
        ),
        Ok(true),
        "each binding must be individually bridge-valid before the swap",
    );

    let swapped = vec![bindings[1].clone(), bindings[0].clone()];
    let before = full_result.clone();
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut full_result,
            Some(&native_trust_ir_bundle),
            &results,
            &swapped,
            &proof_authorities,
        ),
        Ok(false),
    );
    assert_eq!(full_result, before, "swapped bridge bindings must be a transactional no-op");
    assert!(
        !full_result.evidence.iter().any(|evidence| evidence.evidence_id.starts_with("bridge-ay:"))
    );
}

#[test]
fn bridge_unknown_and_failed_rows_preserve_public_carrier_parity() {
    let (function, compiler_contracts, mut vcs) = native_trust_ir_compiler_function();
    let sep_vc = unsafe_sep_assertion_vc(&function.def_path);
    vcs.push(sep_vc.clone());
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("hardened + arithmetic obligations require native TrustIr");
    let sep_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation.metadata.iter().any(|entry| entry.key == "trust.vc.hardened.category")
        })
        .expect("hardened obligation");
    let engine = trust_verifier_api::EngineManifest::new(
        "trust-full-verifier",
        trust_verifier_api::API_VERSION,
        trust_verifier_api::EngineKind::Composite,
    );
    let evidence = bundle
        .obligations
        .iter()
        .map(|obligation| {
            let mut evidence = unsupported_evidence_for(obligation);
            if obligation.obligation_id == sep_obligation.obligation_id {
                evidence.status = trust_verifier_api::EvidenceStatus::Unknown;
            }
            evidence
        })
        .collect::<Vec<_>>();
    let mut unknown_run = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("bridge-unknown-carrier-test").snapshot(),
        &bundle,
        engine,
        &bundle.obligations,
        evidence,
    );
    let failed_run = unknown_run.clone();
    let binding = test_binding_for_obligation(0, &sep_vc, sep_obligation);
    let before_unknown = unknown_run.summary.unknown;
    let before_unsupported = unknown_run.summary.unsupported;
    let proved = vec![(
        sep_vc.clone(),
        VerificationResult::Proved {
            solver: trust_types::Symbol::intern("ay-in-process"),
            time_ms: 1,
            strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(b"p lrat unknown replacement".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let proved_bindings = [binding.clone()];
    let proof_authorities = bridge_test_solver_revalidated_authorities(&proved, &proved_bindings);
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut unknown_run,
            Some(&native_trust_ir_bundle),
            &proved,
            std::slice::from_ref(&binding),
            &proof_authorities,
        ),
        Ok(true),
    );
    assert_eq!(unknown_run.summary.unknown, before_unknown - 1);
    assert_eq!(unknown_run.summary.unsupported, before_unsupported);
    assert!(unknown_run.evidence.iter().any(|evidence| {
        evidence.obligation_id == sep_obligation.obligation_id
            && evidence.status == trust_verifier_api::EvidenceStatus::Proved
    }));
    unknown_run.validate_derived_state().expect("Unknown -> Proved replacement is canonical");
    unknown_run.try_to_manifest().expect("Unknown -> Proved replacement is manifestable");

    // A public definitive verdict is never superseded by bridge evidence. In
    // both directions the append must be a byte-for-byte no-op, including all
    // derived fields, instead of producing two verdicts for one obligation.
    for status in
        [trust_verifier_api::EvidenceStatus::Proved, trust_verifier_api::EvidenceStatus::Failed]
    {
        let mut definitive_run = failed_run.clone();
        let existing = definitive_run
            .evidence
            .iter_mut()
            .find(|evidence| evidence.obligation_id == sep_obligation.obligation_id)
            .expect("target evidence");
        existing.status = status;
        existing.proof_strength = (status == trust_verifier_api::EvidenceStatus::Proved)
            .then(trust_verifier_api::ProofStrength::smt_unsat);
        definitive_run
            .try_reconcile_derived_state()
            .expect("definitive conflict fixture must start canonical");
        definitive_run.validate_derived_state().expect("definitive conflict fixture validates");
        definitive_run.try_to_manifest().expect("definitive conflict fixture is manifestable");
        let before = definitive_run.clone();
        assert_eq!(
            append_bridge_lane_full_verification_evidence(
                &mut definitive_run,
                Some(&native_trust_ir_bundle),
                &proved,
                std::slice::from_ref(&binding),
                &proof_authorities,
            ),
            Ok(false),
            "existing {status:?} evidence must reject a second bridge verdict",
        );
        assert_eq!(definitive_run, before, "conflict rejection must be transactional");
        definitive_run
            .validate_derived_state()
            .expect("definitive conflict rejection leaves canonical state");
        definitive_run
            .try_to_manifest()
            .expect("definitive conflict rejection leaves a lossless manifest");
    }

    // A private bridge refutation has no publishable failed-evidence DAG yet.
    // Keep the public run's honest Unknown evidence instead of relabeling its
    // summary/status from the compiler-only `VerificationResult::Failed`.
    let mut failed_run = failed_run;
    let failed = vec![(
        sep_vc,
        VerificationResult::Failed {
            solver: trust_types::Symbol::intern("ay-in-process"),
            time_ms: 1,
            counterexample: None,
        },
    )];
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut failed_run,
            Some(&native_trust_ir_bundle),
            &failed,
            std::slice::from_ref(&binding),
            &proof_authorities,
        ),
        Ok(false),
    );
    assert!(failed_run.evidence.iter().any(|evidence| {
        evidence.obligation_id == sep_obligation.obligation_id
            && evidence.status == trust_verifier_api::EvidenceStatus::Unknown
    }));
    failed_run.validate_derived_state().expect("private Failed row must not stale public state");
    failed_run.try_to_manifest().expect("private Failed row leaves a lossless public manifest");
}

#[test]
fn bridge_lane_appends_no_evidence_without_retained_artifacts() {
    let (function, compiler_contracts, mut vcs) = native_trust_ir_compiler_function();
    let sep_vc = unsafe_sep_assertion_vc(&function.def_path);
    vcs.push(sep_vc.clone());
    let (bundle, native_trust_ir_bundle) =
        build_full_verification_input_for_tests(&function, &compiler_contracts, &vcs);
    let native_trust_ir_bundle = native_trust_ir_bundle
        .expect("native TrustIr bundle should build")
        .expect("hardened + arithmetic obligations require native TrustIr");
    let mut full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("bridge-evidence-negative-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "test-composite",
            "test",
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        Vec::new(),
    );
    let evidence_before = full_result.evidence.len();

    // (1) ay Proved WITHOUT retained LRAT bytes: no replay/check artifact can
    // be digested from real bytes -> no evidence (fail-closed, row keeps
    // failing the gate).
    // (2) cached ay Proved WITH retained bytes: the session cache currently
    // keys alpha-canonical formula identity, not the exact normalized input
    // materialized below. Until replay rechecks the certificate against the
    // current exact input (or binds an exact-input digest), cached bytes remain
    // inert and cannot publish bridge evidence.
    // (3) clean-kernel-certified Proved: the kernel lane has no solver
    // transcript to retain -> no evidence rather than a forged transcript.
    let results = vec![
        (
            sep_vc.clone(),
            VerificationResult::Proved {
                solver: trust_types::Symbol::intern("ay-in-process"),
                time_ms: 1,
                strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            sep_vc.clone(),
            VerificationResult::Proved {
                solver: trust_types::Symbol::intern("cached:ay-in-process"),
                time_ms: 0,
                strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
                proof_certificate: Some(b"cached-lrat-bytes-without-exact-input-binding".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            sep_vc.clone(),
            VerificationResult::Proved {
                solver: trust_types::Symbol::intern("clean-kernel-certified"),
                time_ms: 1,
                strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
                proof_certificate: Some(b"cic-term".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];
    let sep_obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            obligation.metadata.iter().any(|entry| entry.key == "trust.vc.hardened.category")
        })
        .expect("hardened obligation");
    let result_bindings = vec![
        test_binding_for_obligation(0, &results[0].0, sep_obligation),
        test_binding_for_obligation(1, &results[1].0, sep_obligation),
        test_binding_for_obligation(2, &results[2].0, sep_obligation),
    ];
    let proof_authorities = bridge_test_solver_revalidated_authorities(&results, &result_bindings);
    assert_eq!(
        append_bridge_lane_full_verification_evidence(
            &mut full_result,
            Some(&native_trust_ir_bundle),
            &results,
            &result_bindings,
            &proof_authorities,
        ),
        Ok(false),
    );

    assert_eq!(full_result.evidence.len(), evidence_before);
    assert!(
        !full_result.evidence.iter().any(|evidence| evidence.evidence_id.starts_with("bridge-ay:"))
    );
}

#[test]
fn transport_rows_carry_compiler_design_mandate_bit() {
    // The design-mandate bit is compiler-owned: a hardened-category VC whose
    // violation formula is the tautology `true` (never a discharge target) is
    // flagged; a hardened VC with a real violation formula is not.
    let mandate_vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe] missing SAFETY comment on unsafe block".to_string(),
        },
        function: trust_types::Symbol::intern("demo::m"),
        location: native_trust_ir_test_span(3),
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
    };
    let real_vc = unsafe_sep_assertion_vc("demo::m");
    let results = vec![
        (
            mandate_vc,
            VerificationResult::Unknown {
                solver: trust_types::Symbol::intern("ay-in-process"),
                time_ms: 0,
                reason: "design mandate is not mechanically dischargeable".to_string(),
            },
        ),
        (
            real_vc,
            VerificationResult::Proved {
                solver: trust_types::Symbol::intern("ay-in-process"),
                time_ms: 1,
                strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];

    let rows = build_transport_results_with_runtime_checks(false, &results, None, None);
    assert_eq!(rows.len(), 2);
    assert!(rows[0].design_mandate, "tautology hardened row must carry the mandate bit");
    assert!(!rows[1].design_mandate, "real hardened violation must not carry the mandate bit");
}

// ---------------------------------------------------------------------------
// Trust (green front door, Phase 2 + Phase 3): default-lane assumption demotion.
// ---------------------------------------------------------------------------

/// A transport row marked by the bridge as an EXTERN print/format/write dispatch
/// panic-freedom row (as it appears after `legacy_vc_from_api_obligation` folds the
/// marked obligation description into `VcKind::Assertion { message }`).
fn extern_call_transport_row(outcome: Outcome) -> TransportObligationResult {
    TransportObligationResult {
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "assert".to_string(),
        typed_kind: None,
        description: format!(
            "assertion: {}extern print/format/write dispatch `alloc::fmt::format` runs a user Display/Debug impl that may panic",
            trust_types::assumption::EXTERN_CALL_ASSUMPTION_PREFIX
        ),
        location: None,
        outcome,
        solver: "trust-full-verifier".to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
    }
}

fn plain_transport_row(outcome: Outcome, design_mandate: bool) -> TransportObligationResult {
    TransportObligationResult {
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "assert".to_string(),
        typed_kind: None,
        description: "assertion: some obligation".to_string(),
        location: None,
        outcome,
        solver: "ay-in-process".to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate,
        native_trust_ir: None,
        proof_evidence: None,
    }
}

fn contract_panic_transport_row(outcome: Outcome) -> TransportObligationResult {
    let mut row = plain_transport_row(outcome, false);
    row.description = format!(
        "assertion: {}declared capacity panic",
        trust_types::assumption::CONTRACT_PANIC_VC_MARKER
    );
    row
}

#[test]
fn contract_panic_rows_rewrite_only_in_survey() {
    let mut row = contract_panic_transport_row(Outcome::Failed);
    row.typed_kind = Some(Box::new(VcKind::Assertion {
        message: format!(
            "{}declared capacity panic",
            trust_types::assumption::CONTRACT_PANIC_VC_MARKER
        ),
    }));
    let strict = test_policy(false, false);
    let boundary = test_policy(false, false);
    for (name, policy) in [("strict", strict), ("implicit boundary", boundary)] {
        assert!(
            rewrite_contract_panic_transport_rows(&policy, std::slice::from_ref(&row)).is_none(),
            "{name} must retain the raw failed row; contract panic is not proof"
        );
    }

    let survey = test_policy(true, false);
    let rewritten = rewrite_contract_panic_transport_rows(&survey, std::slice::from_ref(&row))
        .expect("survey must publish conditional contract evidence");
    assert_eq!(rewritten.len(), 1);
    assert_eq!(rewritten[0].kind, trust_types::assumption::CONTRACT_PANIC_MATCHED_ROW_KIND);
    assert_eq!(rewritten[0].outcome, Outcome::Failed, "conditional evidence is never proof");
    assert_eq!(rewritten[0].solver, trust_types::assumption::CONTRACT_PANIC_ROW_SOURCE);
    assert!(
        rewritten[0].typed_kind.is_none(),
        "a synthetic contract-panic classification must not retain the original VC identity"
    );
}

fn failed_test_result() -> VerificationResult {
    VerificationResult::Failed {
        solver: trust_types::Symbol::intern("ay-in-process"),
        time_ms: 3,
        counterexample: None,
    }
}

fn memory_safe_gate_artifacts(
    vc: VerificationCondition,
    result: VerificationResult,
    status: TrustStatus,
    row: TransportObligationResult,
) -> VerificationArtifacts {
    let mut dispositions = IndexVec::new();
    dispositions.push(TrustDisposition {
        kind: TrustObligationKind::Assertion,
        status,
        strength: TrustProofStrength::None,
        certified: false,
    });
    let summary = TrustFunctionSummary::from_dispositions(&dispositions);
    VerificationArtifacts {
        proof_results: TrustProofResults { dispositions, fingerprints: IndexVec::new(), summary },
        telemetry: TrustProofTelemetry { details: IndexVec::new() },
        results: vec![(vc, result)],
        transport_results: vec![row],
        full_verification: None,
        result_bindings: Vec::new(),
        proof_authorities: Vec::new(),
        overflow_check_origins: OverflowCheckOrigins::default(),
    }
}

#[test]
fn memory_safe_failed_panic_gets_authenticated_assumption_row() {
    let results = vec![(test_vc(7), failed_test_result())];
    let mut failed = plain_transport_row(Outcome::Failed, false);
    failed.kind = "divzero".to_string();
    failed.typed_kind = Some(Box::new(VcKind::DivisionByZero));
    failed.claim_digest_sha256 = Some("real-vc-claim-digest".to_string());
    failed.native_trust_ir = Some(test_transport_native_trust_ir());
    failed.proof_evidence = Some(test_transport_proof_evidence());

    let rewritten = rewrite_memory_safe_panic_refutation_rows(true, &results, &[failed])
        .expect("safe failed panic must be reclassified");
    assert_eq!(rewritten.len(), 1);
    assert_eq!(
        rewritten[0].kind,
        format!("assumption:{}", trust_types::assumption::MEMORY_SAFE_PANIC_ASSUMPTION_TAG)
    );
    assert_eq!(rewritten[0].outcome, Outcome::Skipped);
    assert_eq!(rewritten[0].solver, trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE);
    assert!(rewritten[0].native_trust_ir.is_none());
    assert!(rewritten[0].proof_evidence.is_none());
    assert!(
        rewritten[0].typed_kind.is_none(),
        "a synthetic memory-safe assumption must not retain the original VC identity"
    );
    assert!(
        rewritten[0].claim_digest_sha256.is_none(),
        "a synthetic assumption must not retain the real VC's claim authority"
    );
    assert!(
        native_lowering_collapse_keeps_row(&rewritten[0]),
        "a later native-lowering collapse must retain the explicit safe-panic assumption"
    );

    let artifacts = memory_safe_gate_artifacts(
        test_vc(7),
        failed_test_result(),
        TrustStatus::Failed,
        plain_transport_row(Outcome::Failed, false),
    );
    assert!(
        !memory_safe_artifacts_have_non_demotable_failure(&artifacts, &rewritten),
        "raw trustc must accept the same authenticated safe-panic assumption as Targo"
    );
    assert!(
        memory_safe_artifacts_have_non_demotable_failure(&artifacts, &artifacts.transport_results),
        "the raw failed row must remain fatal until it is actually reclassified"
    );
}

#[test]
fn memory_safe_rewrite_never_touches_unsafe_or_disabled_policy_rows() {
    let failed = plain_transport_row(Outcome::Failed, false);
    let safe_results = vec![(test_vc(8), failed_test_result())];
    assert!(
        rewrite_memory_safe_panic_refutation_rows(false, &safe_results, &[failed.clone()])
            .is_none(),
        "an unsafe body/default policy passes enabled=false and must stay strict"
    );

    let mut unsafe_vc = test_vc(9);
    unsafe_vc.kind = VcKind::UnsafeOperation { desc: "raw pointer dereference".to_string() };
    let unsafe_results = vec![(unsafe_vc, failed_test_result())];
    assert!(
        rewrite_memory_safe_panic_refutation_rows(true, &unsafe_results, &[failed]).is_none(),
        "UB-class rows remain failed even if a caller incorrectly asks the pure helper to demote"
    );
}

#[test]
fn memory_safe_rewrite_rejects_contract_and_nonpanic_l0_failures() {
    let failed = plain_transport_row(Outcome::Failed, false);
    let mut contract_vc = test_vc(10);
    contract_vc.kind = VcKind::Assertion {
        message: format!("{}declared panic", trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
    };
    let contract_row = contract_panic_transport_row(Outcome::Failed);
    assert!(
        rewrite_memory_safe_panic_refutation_rows(
            true,
            &[(contract_vc.clone(), failed_test_result())],
            std::slice::from_ref(&contract_row),
        )
        .is_none(),
        "contract-panic evidence keeps its separate fail-closed protocol"
    );
    let contract_artifacts = memory_safe_gate_artifacts(
        contract_vc,
        failed_test_result(),
        TrustStatus::Failed,
        contract_row.clone(),
    );
    assert!(
        memory_safe_artifacts_have_non_demotable_failure(
            &contract_artifacts,
            std::slice::from_ref(&contract_row),
        ),
        "memory-safe must reject contract-panic conditional evidence"
    );

    let mut allocation_vc = test_vc(11);
    allocation_vc.kind = VcKind::UnboundedAllocation {
        callee: "Vec::with_capacity".to_string(),
        count: "1 << 30".to_string(),
        detail: "exceeds configured allocation budget".to_string(),
    };
    assert!(
        rewrite_memory_safe_panic_refutation_rows(
            true,
            &[(allocation_vc, failed_test_result())],
            &[failed],
        )
        .is_none(),
        "availability/design failures are not Rust runtime-panic assumptions"
    );
}

#[test]
fn memory_safe_gate_accepts_only_authenticated_lowering_gap() {
    let mut unsupported_vc = test_vc(12);
    unsupported_vc.kind = VcKind::UnsupportedMir {
        kind: "FullVerification::Assertion".to_string(),
        detail: "native typed lowering did not complete".to_string(),
    };
    let unknown = VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("trust-full-verifier"),
        time_ms: 0,
        reason: "lowering failed".to_string(),
    };
    let raw = plain_transport_row(Outcome::Unknown, false);
    let artifacts =
        memory_safe_gate_artifacts(unsupported_vc, unknown, TrustStatus::Unknown, raw.clone());
    let mut marked = raw;
    marked.kind = format!("assumption:{}", trust_types::assumption::NATIVE_LOWERING_ASSUMPTION_TAG);
    marked.outcome = Outcome::Skipped;
    marked.solver = trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE.to_string();
    assert!(!memory_safe_artifacts_have_non_demotable_failure(&artifacts, &[marked]));

    let unmarked = plain_transport_row(Outcome::Unknown, false);
    assert!(memory_safe_artifacts_have_non_demotable_failure(&artifacts, &[unmarked]));
}

#[test]
fn memory_safe_zero_data_obligations_still_rejects_coroutine_protocol_premise() {
    let dispositions: IndexVec<ObligationId, TrustDisposition> = IndexVec::new();
    let summary = TrustFunctionSummary::from_dispositions(&dispositions);
    let artifacts = VerificationArtifacts {
        proof_results: TrustProofResults { dispositions, fingerprints: IndexVec::new(), summary },
        telemetry: TrustProofTelemetry { details: IndexVec::new() },
        results: Vec::new(),
        transport_results: Vec::new(),
        full_verification: None,
        result_bindings: Vec::new(),
        proof_authorities: Vec::new(),
        overflow_check_origins: OverflowCheckOrigins::default(),
    };
    assert!(
        !memory_safe_artifacts_have_non_demotable_failure(&artifacts, &[]),
        "a genuinely obligation-free safe function remains admissible"
    );

    let mut coroutine = plain_transport_row(Outcome::Skipped, false);
    coroutine.kind = "assumption:coroutine".to_string();
    coroutine.description = "unverified coroutine executor protocol".to_string();
    coroutine.solver = "trust-classifier".to_string();
    assert!(transport_row_is_coroutine_protocol_assumption(&coroutine));
    assert!(
        memory_safe_artifacts_have_non_demotable_failure(&artifacts, &[coroutine]),
        "a synthetic protocol premise must not disappear behind summary.total == 0"
    );
}

/// F2 pin: strict batteries-on enforcement NEVER demotes, for every gap shape —
/// its transport rows stay byte-identical.
#[test]
fn strict_lane_never_demotes_any_gap() {
    for lowering_failed in [true, false] {
        for has_extern in [true, false] {
            for others_proved in [true, false] {
                assert_eq!(
                    default_lane_demotion_decision(
                        /*strict_enforcement=*/ true,
                        /*fmt_format_demotable=*/ false,
                        /*memory_safe=*/ true,
                        lowering_failed,
                        has_extern,
                        others_proved,
                    ),
                    DefaultLaneDemotion::None,
                    "strict lane must never demote a non-fmt::format gap (lowering_failed={lowering_failed}, has_extern={has_extern}, others_proved={others_proved})"
                );
            }
        }
    }
}

/// W2.1: an unsafe function (memory_safe=false) never demotes — an unmodeled unsafe
/// gap could be undefined behavior, so it stays fail-closed.
#[test]
fn unsafe_function_never_demotes() {
    assert_eq!(
        default_lane_demotion_decision(
            false, /*fmt_format_demotable=*/ false, /*memory_safe=*/ false, true, false,
            false
        ),
        DefaultLaneDemotion::None
    );
    assert_eq!(
        default_lane_demotion_decision(
            false, /*fmt_format_demotable=*/ false, /*memory_safe=*/ false, false, true,
            true
        ),
        DefaultLaneDemotion::None
    );
}

/// W2.1: a native lowering failure in the advisory memory-safe lane demotes to the
/// native-lowering backstop.
#[test]
fn native_lowering_failure_demotes_to_backstop() {
    assert_eq!(
        default_lane_demotion_decision(
            false, /*fmt_format_demotable=*/ false, true, /*lowering_failed=*/ true,
            false, false
        ),
        DefaultLaneDemotion::NativeLowering
    );
}

/// W3.5/W3.6: extern-call demotes ONLY when a marked row exists AND every other
/// counted obligation is Proved; otherwise fail-closed (stay UNKNOWN).
#[test]
fn extern_call_demotes_only_when_fail_closed_gate_holds() {
    // Marked extern-call row + all others proved → demote (memory-safe lane).
    assert_eq!(
        default_lane_demotion_decision(
            false, /*fmt_format_demotable=*/ false, /*memory_safe=*/ true, false,
            /*has_extern=*/ true, /*others_proved=*/ true,
        ),
        DefaultLaneDemotion::ExternCall
    );
    // Marked extern-call row but a genuine unresolved obligation remains → fail-closed.
    assert_eq!(
        default_lane_demotion_decision(
            false, false, /*memory_safe=*/ true, false, true, /*others_proved=*/ false
        ),
        DefaultLaneDemotion::None
    );
    // No extern-call row and lowering succeeded → nothing to demote.
    assert_eq!(
        default_lane_demotion_decision(
            false, false, /*memory_safe=*/ true, false, /*has_extern=*/ false, true
        ),
        DefaultLaneDemotion::None
    );
}

/// The extern-call row detector keys on the marker prefix AND non-proved outcome.
#[test]
fn extern_call_row_detection() {
    assert!(transport_row_is_unproved_extern_call(&extern_call_transport_row(Outcome::Unknown)));
    // A proved row is never demoted, even if marked.
    assert!(!transport_row_is_unproved_extern_call(&extern_call_transport_row(Outcome::Proved)));
    // An unmarked unknown row is not an extern-call row.
    assert!(!transport_row_is_unproved_extern_call(&plain_transport_row(Outcome::Unknown, false)));
}

/// W3.6 fail-closed gate: mandate rows and the extern-call rows themselves are
/// excluded; any OTHER unresolved obligation blocks the demotion.
#[test]
fn extern_call_others_all_proved_gate() {
    // mandate(unknown) + extern-call(unknown) + one proved → gate open.
    let ok = vec![
        plain_transport_row(Outcome::Unknown, /*design_mandate=*/ true),
        extern_call_transport_row(Outcome::Unknown),
        plain_transport_row(Outcome::Proved, false),
    ];
    assert!(extern_call_demotion_others_all_proved(&ok));
    // Add a genuine non-mandate unknown → gate closed (fail-closed).
    let blocked = vec![extern_call_transport_row(Outcome::Unknown), plain_transport_row(Outcome::Unknown, false)];
    assert!(!extern_call_demotion_others_all_proved(&blocked));
    // A failed non-mandate row also blocks.
    let failed = vec![extern_call_transport_row(Outcome::Unknown), plain_transport_row(Outcome::Failed, false)];
    assert!(!extern_call_demotion_others_all_proved(&failed));
}

// ---------------------------------------------------------------------------
// FIX b59 — FIX 1: fail-closed / survey-lane `fmt::format` extern-dispatch demotion.
// ---------------------------------------------------------------------------

/// A `_print` (stdout) extern-dispatch row — the SIGPIPE-hazard leg the safe
/// `fmt::format` subset must EXCLUDE.
fn stdout_print_extern_call_transport_row(outcome: Outcome) -> TransportObligationResult {
    let mut row = extern_call_transport_row(outcome);
    row.description = format!(
        "assertion: {}extern print/format/write dispatch `std::io::_print` runs a user Display/Debug impl that may panic",
        trust_types::assumption::EXTERN_CALL_ASSUMPTION_PREFIX
    );
    row
}

/// FIX b59: the safe `fmt::format` subset demotes in BOTH the strict fail-closed lane
/// AND the survey non-memory-safe lane (the `ny-cert` lane), not only the
/// memory-safe lane — while a non-demotable case stays fail-closed / UNKNOWN.
#[test]
fn fmt_format_subset_demotes_in_fail_closed_and_survey_lanes() {
    // Strict fail-closed lane: the safe fmt::format subset still demotes.
    assert_eq!(
        default_lane_demotion_decision(
            /*strict_enforcement=*/ true, /*fmt_format_demotable=*/ true,
            /*memory_safe=*/ false, /*lowering_failed=*/ false,
            /*has_extern=*/ true, /*others_proved=*/ true,
        ),
        DefaultLaneDemotion::FmtFormat
    );
    // Survey WITHOUT the memory-safe flag (the ny-cert lane): also demotes.
    assert_eq!(
        default_lane_demotion_decision(false, true, /*memory_safe=*/ false, false, true, true),
        DefaultLaneDemotion::FmtFormat
    );
    // Not demotable (a guard pin was unmet) → stays fail-closed / UNKNOWN in both lanes.
    assert_eq!(
        default_lane_demotion_decision(
            true, /*fmt_format_demotable=*/ false, false, false, true, true
        ),
        DefaultLaneDemotion::None
    );
    assert_eq!(
        default_lane_demotion_decision(
            false, /*fmt_format_demotable=*/ false, false, false, true, true
        ),
        DefaultLaneDemotion::None
    );
}

/// FIX b59: the demotion gate pins ALL THREE conditions — a `fmt::format` row, an
/// unsafe-free function, and every other obligation proved. Any one false keeps the
/// function fail-closed (never mask an unsafe UB gap or a real sibling failure).
#[test]
fn fmt_format_gate_requires_all_three_pins() {
    assert!(fmt_format_demotion_gate(
        /*has_fmt_format=*/ true, /*function_is_unsafe_free=*/ true,
        /*others_all_proved=*/ true
    ));
    // No fmt::format row → nothing to demote.
    assert!(!fmt_format_demotion_gate(false, true, true));
    // The function contains `unsafe` → an unsafe gap could be UB the fmt panic masks.
    assert!(!fmt_format_demotion_gate(true, false, true));
    // Another obligation is unproved → fail-closed, never mask a real failure.
    assert!(!fmt_format_demotion_gate(true, true, false));
}

/// FIX b59: the safe subset is scoped to the `fmt::format` callee — the `_print`/
/// `_eprint` stdout legs (SIGPIPE hazard) are NOT eligible, and a proved row never
/// demotes.
#[test]
fn fmt_format_extern_call_scopes_to_format_not_stdout() {
    // The `alloc::fmt::format` (format! backend) leg IS the safe subset.
    assert!(transport_row_is_unproved_fmt_format_extern_call(&extern_call_transport_row(Outcome::Unknown
    )));
    // A proved fmt::format row is never demoted.
    assert!(!transport_row_is_unproved_fmt_format_extern_call(&extern_call_transport_row(Outcome::Proved
    )));
    // The stdout `_print` leg is an extern-call row but NOT in the safe subset.
    assert!(transport_row_is_unproved_extern_call(&stdout_print_extern_call_transport_row(Outcome::Unknown
    )));
    assert!(!transport_row_is_unproved_fmt_format_extern_call(
        &stdout_print_extern_call_transport_row(Outcome::Unknown)
    ));
    // A non-extern-call row is not a fmt::format row.
    assert!(!transport_row_is_unproved_fmt_format_extern_call(&plain_transport_row(Outcome::Unknown, false
    )));
    // The callee extractor reads the backtick-delimited callee.
    assert_eq!(
        extern_call_row_callee(&extern_call_transport_row(Outcome::Unknown).description),
        Some("alloc::fmt::format")
    );
}

// ---------------------------------------------------------------------------
// FIX b59 — FIX 2: bounded transitive structural-drop field-type closure.
// ---------------------------------------------------------------------------

/// FIX b59: an `Option<serde_json::Value>`-shaped nested-no-`Drop` type graph closes
/// FULLY — every transitively-nested no-`Drop` node (including a cyclic `Value`) is
/// recorded, so the bridge's drop-glue gate can recurse the whole tree and prove it
/// panic-free. This is the exact gap the old `ty::walk()` (generic-args-only) missed.
#[test]
fn structural_drop_closure_records_all_transitive_no_drop_nodes() {
    // option -> value ; value -> {number, string, vec_value, map} ;
    // vec_value -> value (cycle) ; map -> {string, value} ; all no-`Drop`.
    let graph: FxHashMap<&str, Vec<&str>> = [
        ("option", vec!["value"]),
        ("value", vec!["number", "string", "vec_value", "map"]),
        ("number", vec![]),
        ("string", vec![]),
        ("vec_value", vec!["value"]),
        ("map", vec!["string", "value"]),
    ]
    .into_iter()
    .collect();
    let mut out: FxHashSet<&str> = FxHashSet::default();
    drive_structural_drop_closure(
        "option",
        1024,
        |_n| false, // no node has a user Drop impl
        |n| {
            out.insert(*n);
        },
        |n| graph.get(n).cloned().unwrap_or_default(),
    );
    for node in ["option", "value", "number", "string", "vec_value", "map"] {
        assert!(out.contains(node), "transitively-nested no-Drop node `{node}` must be recorded");
    }
}

/// FIX b59: the fail-closed DTOR pin — a node WITH a user `Drop` impl is NEVER
/// recorded and its subtree is CUT, so the bridge (which declines any node absent
/// from the set) still fails closed on it. A type with a real `Drop` never becomes
/// structural.
#[test]
fn structural_drop_closure_cuts_drop_bearing_subtree() {
    let graph: FxHashMap<&str, Vec<&str>> = [
        ("root", vec!["plain", "dropper"]),
        ("plain", vec!["leaf"]),
        ("leaf", vec![]),
        ("dropper", vec!["under_dropper"]),
        ("under_dropper", vec![]),
    ]
    .into_iter()
    .collect();
    let mut out: FxHashSet<&str> = FxHashSet::default();
    drive_structural_drop_closure(
        "root",
        1024,
        |n| *n == "dropper", // only `dropper` carries a user Drop impl
        |n| {
            out.insert(*n);
        },
        |n| graph.get(n).cloned().unwrap_or_default(),
    );
    assert!(out.contains("plain") && out.contains("leaf"), "no-Drop nodes are recorded");
    assert!(!out.contains("dropper"), "a Drop-bearing node is never structural");
    assert!(
        !out.contains("under_dropper"),
        "the subtree under a Drop-bearing node is cut — fail-closed"
    );
}

/// FIX b59: the FUEL pin — a fuel-bail stops the closure, leaving deeper nodes
/// unrecorded (fail-closed, never a false structural PROVE); and a cyclic graph
/// terminates via the visited-set.
#[test]
fn structural_drop_closure_fuel_bails_closed_and_terminates() {
    // A long chain 0 -> 1 -> ... -> 99.
    let chain: FxHashMap<u32, Vec<u32>> = (0u32..100).map(|i| (i, vec![i + 1])).collect();
    let mut out: FxHashSet<u32> = FxHashSet::default();
    drive_structural_drop_closure(
        0u32,
        3, // only three pops of budget
        |_n| false,
        |n| {
            out.insert(*n);
        },
        |n| chain.get(n).cloned().unwrap_or_default(),
    );
    assert!(out.len() <= 3, "fuel bounds the recorded nodes to the pop budget");
    assert!(!out.contains(&50), "a fuel-bail leaves deep nodes unrecorded — fail-closed");

    // A 2-cycle a <-> b terminates and records both.
    let cyc: FxHashMap<&str, Vec<&str>> =
        [("a", vec!["b"]), ("b", vec!["a"])].into_iter().collect();
    let mut cyc_out: FxHashSet<&str> = FxHashSet::default();
    drive_structural_drop_closure(
        "a",
        1024,
        |_n| false,
        |n| {
            cyc_out.insert(*n);
        },
        |n| cyc.get(n).cloned().unwrap_or_default(),
    );
    assert_eq!(cyc_out.len(), 2, "the visited-set makes a cyclic graph terminate");
}

fn absent_callee_transport_row(outcome: Outcome) -> TransportObligationResult {
    TransportObligationResult {
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "assert".to_string(),
        typed_kind: None,
        description: format!(
            "assertion: {}call to absent callee `core::num::u32::pow` (body not in the lowered bundle) may panic",
            trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX
        ),
        location: None,
        outcome,
        solver: "trust-full-verifier".to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
    }
}

fn expected_absent_callee_transport_row(outcome: Outcome) -> TransportObligationResult {
    let mut row = absent_callee_transport_row(outcome);
    row.description = format!(
        "assertion: {}call to user-skipped callee `demo::skipped` may panic",
        trust_types::assumption::EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX
    );
    row
}

fn drop_glue_transport_row(outcome: Outcome) -> TransportObligationResult {
    TransportObligationResult {
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "assert".to_string(),
        typed_kind: None,
        description: format!(
            "assertion: {}drop glue for `NeedsDrop` has unproven panic-freedom (user Drop impls may panic)",
            trust_types::assumption::DROP_GLUE_ASSUMPTION_PREFIX
        ),
        location: None,
        outcome,
        solver: "trust-full-verifier".to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
    }
}

/// Expected-absent bookkeeping must use the exact extractor call key, not a
/// reconstructed display path that loses instantiation or crate identity.
#[test]
fn expected_absent_identity_preserves_generic_and_crate_disambiguation_bytes() {
    let call_key = "shared@8f03a115::audit::total::<alloc::vec::Vec<u8>>#args@9c20be7d";
    let mut identities = FxHashSet::default();
    insert_exact_absent_call_identity(&mut identities, call_key);

    assert_eq!(identities.len(), 1);
    assert!(identities.contains(call_key));
    assert!(
        !identities.contains("shared::audit::total"),
        "collector bookkeeping must never collapse an extractor call key to safe_def_path_str"
    );
}

/// Trust: fail-closed on absent-callee / expected-absent / drop-glue panic
/// (revert of d8a9bbc28e / d848dcad97 fail-open). An UNPROVEN panic-freedom row
/// in any of these classes is fatal in the fail-closed lane.
/// A `proved` row is never such a gap (the reachable-panic marker forbids `proved`
/// in practice, but the predicate keys on outcome for defense-in-depth), and an
/// unmarked / extern-call row is not this class.
#[test]
fn absent_expected_absent_and_drop_glue_unproved_rows_are_fatal() {
    // The unproved absent-callee row is detected as a fatal panic gap.
    assert!(transport_row_is_unproved_assumption_panic(&absent_callee_transport_row(Outcome::Unknown)));
    assert!(transport_row_is_unproved_assumption_panic(&absent_callee_transport_row(Outcome::RuntimeChecked
    )));
    assert!(transport_row_is_unproved_assumption_panic(&expected_absent_callee_transport_row(Outcome::Unknown
    )));
    // The unproved drop-glue row too.
    assert!(transport_row_is_unproved_assumption_panic(&drop_glue_transport_row(Outcome::Unknown)));
    // A proved row (never actually emitted for this class, but keyed on for safety)
    // is not a gap.
    assert!(!transport_row_is_unproved_assumption_panic(&absent_callee_transport_row(Outcome::Proved)));
    assert!(!transport_row_is_unproved_assumption_panic(&expected_absent_callee_transport_row(Outcome::Proved
    )));
    assert!(!transport_row_is_unproved_assumption_panic(&drop_glue_transport_row(Outcome::Proved)));
    // A plain obligation and an extern-call row are a DIFFERENT class — not this
    // fail-closed panic gap (extern-call has its own W3.5/W3.6 demotion gate).
    assert!(!transport_row_is_unproved_assumption_panic(&plain_transport_row(Outcome::Unknown, false)));
    assert!(!transport_row_is_unproved_assumption_panic(&extern_call_transport_row(Outcome::Unknown)));

    // The batch predicate fires when ANY row is an unproved assumption panic.
    assert!(transport_rows_have_unproved_assumption_panic(&[
        plain_transport_row(Outcome::Proved, false),
        absent_callee_transport_row(Outcome::Unknown),
    ]));
    assert!(transport_rows_have_unproved_assumption_panic(&[
        plain_transport_row(Outcome::Proved, false),
        expected_absent_callee_transport_row(Outcome::Unknown),
    ]));
    assert!(transport_rows_have_unproved_assumption_panic(&[
        plain_transport_row(Outcome::Proved, false),
        drop_glue_transport_row(Outcome::Unknown),
    ]));
    // A clean set (only proofs + an extern-call gap that has its own path) does not
    // trip the absent-callee/drop-glue fatality.
    assert!(!transport_rows_have_unproved_assumption_panic(&[
        plain_transport_row(Outcome::Proved, false),
        extern_call_transport_row(Outcome::Unknown),
    ]));
}

#[test]
fn expected_absent_callee_demotes_only_in_survey() {
    let rows = [expected_absent_callee_transport_row(Outcome::Unknown)];
    let strict = test_policy(false, false);
    let boundary = test_policy(false, false);
    assert!(!expected_absent_callee_demotion_applies(&strict, &rows));
    assert!(!expected_absent_callee_demotion_applies(&boundary, &rows));

    let survey = test_policy(true, false);
    assert!(expected_absent_callee_demotion_applies(&survey, &rows));

    assert!(
        !vc_kind_is_memory_safe_demotable_gap(&VcKind::Assertion {
            message: rows[0].description.clone(),
        }),
        "memory-safe must not authenticate an expected-absent assumption"
    );
}

fn bool_true_formula_payload() -> String {
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::bool_literal(true),
        Vec::new(),
    );
    serde_json::to_string(&predicate).expect("serialize Bool(true) predicate")
}

fn real_violation_formula_payload() -> String {
    // A genuine (non-tautology) hardened assert violation: `1 < 0`.
    let expr = trust_verifier_api::TrustSpecExpr::binary(
        trust_verifier_api::TrustSpecBinaryOp::Lt,
        trust_verifier_api::TrustSpecExpr::int_literal("1"),
        trust_verifier_api::TrustSpecExpr::int_literal("0"),
    );
    let predicate = trust_verifier_api::TrustSpecPredicate::new(expr, Vec::new());
    serde_json::to_string(&predicate).expect("serialize real predicate")
}

fn hardened_obligation_with_payload(
    payload: Option<String>,
) -> trust_verifier_api::TrustObligation {
    let mut metadata = vec![trust_verifier_api::MetadataEntry {
        key: TRUST_VC_HARDENED_CATEGORY_METADATA_KEY.to_string(),
        value: "process_semantics".to_string(),
    }];
    if let Some(payload) = payload {
        metadata.push(trust_verifier_api::MetadataEntry {
            key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
            value: payload,
        });
    }
    trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo:hardened_boundary:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.hardened".to_string(),
            name: "process_semantics".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "hardened boundary (process_semantics): _print".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata,
    }
}

/// W3.7/F4: a hardened obligation whose violation payload is the tautology
/// `Bool(true)` is a DESIGN MANDATE; a real (`1 < 0`) violation and an absent
/// payload are NOT (fail-closed — a genuine discharge target).
#[test]
fn hardened_design_mandate_detection() {
    assert!(hardened_obligation_is_design_mandate(&hardened_obligation_with_payload(Some(
        bool_true_formula_payload()
    ))));
    assert!(!hardened_obligation_is_design_mandate(&hardened_obligation_with_payload(Some(
        real_violation_formula_payload()
    ))));
    assert!(!hardened_obligation_is_design_mandate(&hardened_obligation_with_payload(None)));
}

/// Native VC reconstruction must validate the complete typed-predicate schema,
/// not merely deserialize the expression tree. Otherwise an undeclared name or
/// a declaration/node sort disagreement becomes solver input with authority the
/// producer never established.
#[test]
fn malformed_typed_formula_payloads_fail_closed_before_native_reconstruction() {
    let undeclared = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::variable(
            "missing",
            trust_verifier_api::TrustSpecSort::Bool,
        ),
        Vec::new(),
    );
    assert!(undeclared.validate().is_err(), "fixture must be structurally invalid");

    let undeclared_obligation = hardened_obligation_with_payload(Some(
        serde_json::to_string(&undeclared).expect("invalid predicate still has valid JSON"),
    ));
    assert!(
        reconstruct_obligation_violation_formula(&undeclared_obligation).is_none(),
        "an undeclared variable must not become a reconstructed native VC"
    );

    let inconsistent = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::variable(
            "flag",
            trust_verifier_api::TrustSpecSort::Bool,
        ),
        vec![trust_verifier_api::TrustSpecVariable {
            name: "flag".to_string(),
            sort: trust_verifier_api::TrustSpecSort::Int,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
        }],
    );
    assert!(inconsistent.validate().is_err(), "fixture must carry inconsistent sorts");

    let inconsistent_obligation = hardened_obligation_with_payload(Some(
        serde_json::to_string(&inconsistent).expect("invalid predicate still has valid JSON"),
    ));
    assert!(
        reconstruct_obligation_violation_formula(&inconsistent_obligation).is_none(),
        "a forged expression-node sort must not become a reconstructed native VC"
    );

    let (function, _, _) = native_trust_ir_compiler_function();
    for malformed in [&undeclared_obligation, &inconsistent_obligation] {
        let vc = legacy_vc_from_api_obligation(&function, malformed);
        assert!(
            matches!(vc.formula, trust_types::Formula::Bool(false)),
            "malformed metadata must retain the fail-closed placeholder; got {:?}",
            vc.formula
        );
    }
}

/// The design-mandate classifier is another metadata consumer and must apply
/// the same full validation. A `true` root cannot hide an invalid declaration
/// table and acquire mandate status.
#[test]
fn malformed_typed_formula_cannot_acquire_design_mandate_status() {
    let variable = trust_verifier_api::TrustSpecVariable {
        name: "duplicate".to_string(),
        sort: trust_verifier_api::TrustSpecSort::Bool,
        origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
    };
    let malformed = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::bool_literal(true),
        vec![variable.clone(), variable],
    );
    assert!(malformed.validate().is_err(), "fixture must have duplicate declarations");
    let obligation = hardened_obligation_with_payload(Some(
        serde_json::to_string(&malformed).expect("invalid predicate still has valid JSON"),
    ));
    assert!(
        !hardened_obligation_is_design_mandate(&obligation),
        "invalid metadata must never acquire design-mandate semantics"
    );
}

/// Public obligation metadata is a map-shaped carrier: duplicate formula keys
/// are invalid and must not be resolved by insertion order in either native
/// reconstruction consumer.
#[test]
fn duplicate_typed_formula_metadata_fails_closed_before_native_reconstruction() {
    let mut duplicated_mandate =
        hardened_obligation_with_payload(Some(bool_true_formula_payload()));
    duplicated_mandate.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
        value: real_violation_formula_payload(),
    });
    assert!(
        !hardened_obligation_is_design_mandate(&duplicated_mandate),
        "the first of two formula payloads must not control mandate classification"
    );

    let mut duplicated_violation =
        hardened_obligation_with_payload(Some(real_violation_formula_payload()));
    duplicated_violation.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
        value: bool_true_formula_payload(),
    });
    assert!(
        reconstruct_obligation_violation_formula(&duplicated_violation).is_none(),
        "the first of two formula payloads must not become a reconstructed VC"
    );

    let (function, _, _) = native_trust_ir_compiler_function();
    let vc = legacy_vc_from_api_obligation(&function, &duplicated_violation);
    assert!(
        matches!(vc.formula, trust_types::Formula::Bool(false)),
        "duplicate formula metadata must retain the fail-closed placeholder; got {:?}",
        vc.formula
    );
}

/// A direct TrustVC counterexample to a violation-pruned payload is not a
/// counterexample to the original violation: pruning drops conjuncts, so the
/// selected formula has more models. Only one exact canonical pruning marker
/// may trigger that downgrade, and only one exact refutation marker may carry
/// direct-refutation authority.
fn legacy_result_without_native_rows(
    obligation: &trust_verifier_api::TrustObligation,
) -> VerificationResult {
    legacy_result_without_native_rows_with_assumed_total(obligation, false)
}

fn legacy_result_without_native_rows_with_assumed_total(
    obligation: &trust_verifier_api::TrustObligation,
    assumed_total_callee_assumption: bool,
) -> VerificationResult {
    full_verification_legacy_result_for_obligation(
        obligation,
        &FxHashMap::default(),
        &FxHashMap::default(),
        &FxHashSet::default(),
        false,
        assumed_total_callee_assumption,
    )
}

#[test]
fn direct_trust_vc_refutation_honors_unique_exact_pruning_metadata() {
    let mut refuted = hardened_obligation_with_payload(None);
    refuted.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_REFUTED_METADATA_KEY.to_string(),
        value: "model: index=0,len=0".to_string(),
    });
    assert!(
        matches!(legacy_result_without_native_rows(&refuted), VerificationResult::Failed { .. }),
        "an exact direct refutation of an unpruned formula remains Failed"
    );

    let mut pruned = refuted.clone();
    pruned.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_PRUNED_METADATA_KEY.to_string(),
        value: "true".to_string(),
    });
    assert!(
        matches!(
            legacy_result_without_native_rows(&pruned),
            VerificationResult::Unknown { reason, .. }
                if reason.contains("weaker violation-pruned sub-conjunction")
        ),
        "a model of the weaker pruned formula must not refute the original"
    );

    for malformed in ["false", "TRUE", "1", " true "] {
        let mut obligation = refuted.clone();
        obligation.metadata.push(trust_verifier_api::MetadataEntry {
            key: TRUST_VC_FORMULA_PRUNED_METADATA_KEY.to_string(),
            value: malformed.to_string(),
        });
        assert!(
            matches!(
                legacy_result_without_native_rows(&obligation),
                VerificationResult::Failed { .. }
            ),
            "non-canonical pruning marker `{malformed}` must not erase a direct refutation"
        );
    }

    let mut duplicate_pruning_marker = pruned.clone();
    duplicate_pruning_marker.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_FORMULA_PRUNED_METADATA_KEY.to_string(),
        value: "true".to_string(),
    });
    assert!(
        matches!(
            legacy_result_without_native_rows(&duplicate_pruning_marker),
            VerificationResult::Failed { .. }
        ),
        "duplicate pruning metadata must not be resolved by insertion order"
    );

    let mut duplicate_refutation_marker = refuted.clone();
    duplicate_refutation_marker.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_VC_REFUTED_METADATA_KEY.to_string(),
        value: "different model".to_string(),
    });
    assert!(
        matches!(
            legacy_result_without_native_rows(&duplicate_refutation_marker),
            VerificationResult::Unknown { .. }
        ),
        "duplicate refutation metadata cannot carry direct-refutation authority"
    );
}

/// W3.7/F4 root-cause fix: a hardened design mandate reconstructs to a VC whose
/// formula is the tautology `Bool(true)` (so the transport constructor's
/// `design_mandate` bit survives the full-lane reconstruction), while a real
/// hardened violation keeps its reconstructed formula (no mandate bit).
#[test]
fn legacy_vc_restores_design_mandate_formula() {
    let (function, _, _) = native_trust_ir_compiler_function();

    let mandate = hardened_obligation_with_payload(Some(bool_true_formula_payload()));
    let vc = legacy_vc_from_api_obligation(&function, &mandate);
    assert!(vc.kind.hardened_category().is_some(), "mandate must stay hardened-kind");
    assert!(
        matches!(vc.formula, trust_types::Formula::Bool(true)),
        "hardened design mandate must reconstruct with a Bool(true) violation so the \
         design_mandate bit survives; got {:?}",
        vc.formula
    );

    let real = hardened_obligation_with_payload(Some(real_violation_formula_payload()));
    let real_vc = legacy_vc_from_api_obligation(&function, &real);
    assert!(
        !matches!(real_vc.formula, trust_types::Formula::Bool(true)),
        "a real hardened violation must NOT be forced to the design-mandate tautology"
    );
}

/// W2.1 soundness pin: the native-lowering collapse KEEPS genuine proofs and genuine
/// refutations, folding only the poisoned coverage-gap rows — a `failed` refutation
/// must never be hidden behind an `assumption:native-lowering` row.
#[test]
fn native_lowering_collapse_preserves_proofs_and_refutations() {
    assert!(native_lowering_collapse_keeps_row(&plain_transport_row(Outcome::Proved, false)));
    assert!(native_lowering_collapse_keeps_row(&plain_transport_row(Outcome::Failed, false)));
    // Poisoned coverage-gap outcomes fold into the single native-lowering row.
    assert!(!native_lowering_collapse_keeps_row(&plain_transport_row(Outcome::Unknown, false)));
    assert!(!native_lowering_collapse_keeps_row(&plain_transport_row(Outcome::RuntimeChecked, false)));
    assert!(!native_lowering_collapse_keeps_row(&plain_transport_row(Outcome::Skipped, false)));
}

// ---------------------------------------------------------------------------
// Def-site `#[requires]` marker: entry-assumption discharge (P1.2)
// ---------------------------------------------------------------------------

/// A requires-contract function shaped like the regressing production case
/// (`generate::Lcg::range_usize` with `#[trust::requires(lo <= hi)]`): a
/// lowered `Requires` contract whose def-site marker obligation
/// (`obligation:<fn>:precondition:0`, `contract_id: Some(..)`, typed context
/// origin `Contract { contract_kind: Requires }`) routes to trust-wp, whose
/// pure replay honestly returns `Unsupported` on a free `lo <= hi`.
fn requires_marker_function()
-> (trust_types::VerifiableFunction, trust_types::CompilerContractBundle) {
    let contract = trust_types::Contract {
        kind: trust_types::ContractKind::Requires,
        span: trust_types::SourceSpan {
            file: "generate.rs".to_string(),
            line_start: 5,
            col_start: 1,
            line_end: 5,
            col_end: 30,
        },
        body: "__trust_lowered_compiler_contract__:lo <= hi".to_string(),
    };
    let function = trust_types::VerifiableFunction {
        name: "range_usize".to_string(),
        def_path: "generate::Lcg::range_usize".to_string(),
        span: trust_types::SourceSpan {
            file: "generate.rs".to_string(),
            line_start: 6,
            col_start: 1,
            line_end: 10,
            col_end: 2,
        },
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("_0".to_string()),
                },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("lo".to_string()),
                },
                trust_types::LocalDecl {
                    index: 2,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("hi".to_string()),
                },
            ],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: Vec::new(),
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 2,
            return_ty: trust_types::Ty::Int { width: 64, signed: false },
        },
        contracts: vec![contract.clone()],
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    };
    let compiler_contracts = trust_types::CompilerContractBundle::new(vec![contract]);
    (function, compiler_contracts)
}

#[test]
fn compiler_function_and_default_obligation_digests_are_domain_and_content_bound() {
    let (mut function, _) = requires_marker_function();
    let source_before =
        compiler_function_source_digest_hex(&function).expect("function serialization");
    let obligation_before = default_trust_mc_function_obligation_digest(&function, "false")
        .expect("obligation serialization");
    assert_eq!(source_before.len(), 64);
    assert_eq!(obligation_before.len(), 64);
    assert_ne!(source_before, obligation_before, "digest domains must be disjoint");

    function.span.line_end += 1;
    let source_after =
        compiler_function_source_digest_hex(&function).expect("changed function serialization");
    let obligation_after = default_trust_mc_function_obligation_digest(&function, "false")
        .expect("changed obligation serialization");
    assert_ne!(source_before, source_after, "changing function content must change its digest");
    assert_ne!(
        obligation_before, obligation_after,
        "changing bound function content must change the obligation digest"
    );
    assert_ne!(
        obligation_after,
        default_trust_mc_function_obligation_digest(&function, "true")
            .expect("changed payload serialization"),
        "changing the typed payload must change the obligation digest"
    );
    assert_ne!(
        domain_length_bound_sha256_hex("domain-a", b"bc"),
        domain_length_bound_sha256_hex("domain-ab", b"c"),
        "length framing must prevent domain/payload boundary ambiguity"
    );
}

fn unsupported_evidence_for(
    obligation: &trust_verifier_api::TrustObligation,
) -> trust_verifier_api::ObligationEvidence {
    trust_verifier_api::ObligationEvidence {
        evidence_id: format!("unsupported:{}", obligation.obligation_id),
        obligation_id: obligation.obligation_id.clone(),
        engine: trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        status: trust_verifier_api::EvidenceStatus::Unsupported,
        proof_strength: None,
        artifacts: Vec::new(),
        counterexample: None,
        publication: trust_verifier_api::EvidencePublicationMetadata::default(),
        diagnostics: Vec::new(),
    }
}

/// Case-A pin (emitter + discriminator): `contract_bundle_to_verifier_api`
/// emits the def-site `#[requires]` marker as `ObligationKind::Precondition`
/// with `contract_id: Some(..)` AND a `trust.obligation_context.v1` entry whose
/// origin is `Contract { contract_kind: Requires }` — and
/// `is_definition_site_requires_marker` recognizes it. The in-process legacy
/// mapping then discharges it as `Proved(trust-entry-assumption)` even when the
/// native evidence for it is `Unsupported` (the trust-wp pure replay cannot
/// prove a free `lo <= hi` — exactly the production evidence); the transport
/// boundary separately exposes that discharge as an explicit assumption.
#[test]
fn def_site_requires_marker_is_recognized_and_row_discharged() {
    let (function, compiler_contracts) = requires_marker_function();
    let bundle =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &[]);
    let marker = bundle
        .obligations
        .iter()
        .find(|obligation| {
            matches!(obligation.kind, trust_verifier_api::ObligationKind::Precondition)
                && obligation.contract_id.is_some()
        })
        .expect("bundle should contain the def-site requires marker");
    assert!(
        is_definition_site_requires_marker(marker),
        "def-site requires marker must be recognized by its Contract{{Requires}} origin: {marker:#?}"
    );

    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("requires-marker-row-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        vec![unsupported_evidence_for(marker)],
    );
    let reference =
        trust_mir_extract::contract_bundle_to_verifier_api(&function, &compiler_contracts);
    let definition_entry_markers =
        ExactDefinitionEntryMarkerSet::freeze_from_compiler_reference(&reference, &bundle)
            .seal_final_bundle(&bundle);
    let mut snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &compiler_contracts,
        &bundle,
        &[],
        full_result.context.clone(),
    );
    snapshot.definition_entry_markers = definition_entry_markers;
    let legacy_results = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &full_result,
        &[],
        &snapshot,
    )
    .0;
    let marker_row = legacy_results
        .iter()
        .find(|(vc, _)| matches!(&vc.kind, VcKind::UnsupportedMir { detail, .. } if detail.contains("requires contract")))
        .expect("marker legacy row must exist");
    assert!(
        matches!(
            &marker_row.1,
            VerificationResult::Proved { solver, .. }
                if solver.as_str() == TRUST_ENTRY_ASSUMPTION_SOLVER
        ),
        "def-site requires marker must be discharged as the entry assumption on the row path: {marker_row:#?}"
    );
}

/// Default-lane VC-skip provenance must distinguish the function's own
/// source-indexed entry marker from a recursive call to that same function.
/// Both rows have `callee == function`; only the former is regenerated from
/// the canonical authored `Requires` clause byte-for-byte.
#[test]
fn default_lane_entry_assumption_requires_exact_regenerated_source_identity() {
    let (function, _) = requires_marker_function();
    let regenerated = exact_definition_entry_assumption_rows(&function);
    assert_eq!(regenerated.len(), 1, "one requires clause must mint one exact entry row");
    let marker = regenerated[0].clone();
    assert!(is_exact_definition_entry_assumption_row(&marker, &regenerated));
    let unknown = || VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("fresh-context-test"),
        time_ms: 0,
        reason: "not discharged".to_string(),
    };
    let unique_supplied = vec![(marker.clone(), unknown())];
    assert!(is_unique_exact_result_row(&marker, &exact_result_row_counts(&unique_supplied)));
    let duplicate_supplied = vec![(marker.clone(), unknown()), (marker.clone(), unknown())];
    assert!(
        !is_unique_exact_result_row(&marker, &exact_result_row_counts(&duplicate_supplied)),
        "duplicate supplied rows must not inherit the unique regenerated marker's exemption"
    );
    assert_eq!(
        marker.contract_metadata.and_then(|metadata| metadata.source_contract_index),
        Some(0),
        "the exemption must be bound to the dense source contract index"
    );

    let mut recursive_call = marker.clone();
    recursive_call.contract_metadata = None;
    recursive_call.formula = trust_types::Formula::Var(
        "recursive_call_establishes_requires".to_string(),
        trust_types::Sort::Bool,
    );
    assert!(matches!(
        &recursive_call.kind,
        VcKind::Precondition { callee } if callee == &function.name
    ));
    assert_eq!(recursive_call.function.as_str(), function.name);
    assert!(
        !is_exact_definition_entry_assumption_row(&recursive_call, &regenerated),
        "a recursive call-site precondition must never inherit the definition-entry skip"
    );
    assert_eq!(
        fail_closed_unproved_precondition(&recursive_call.kind, TrustStatus::Unknown, false),
        TrustStatus::Failed,
        "an unresolved recursive precondition must be fatal"
    );
    assert_eq!(
        fail_closed_unproved_precondition(&marker.kind, TrustStatus::Unknown, true),
        TrustStatus::Unknown,
        "only the exact definition-entry bookkeeping row keeps its non-obligation status"
    );
    assert_eq!(
        fail_closed_unproved_precondition(&recursive_call.kind, TrustStatus::Certified, false),
        TrustStatus::Certified,
        "a genuinely certified caller obligation must remain certified"
    );

    let mut forged_index = marker.clone();
    forged_index.contract_metadata.as_mut().expect("marker metadata").source_contract_index =
        Some(usize::MAX);
    assert!(!is_exact_definition_entry_assumption_row(&forged_index, &regenerated));

    assert!(
        !is_exact_definition_entry_assumption_row(&marker, &[marker.clone(), marker.clone()]),
        "ambiguous regenerated identities must fail closed"
    );
}

/// SOUNDNESS pin: a CALL-SITE precondition obligation — even one carrying the
/// callee's `contract_id` (the trust-wp typed-contract binding rewrites
/// `contract_id` on caller-side VC obligations) — has typed context origin
/// `VerificationCondition` and must NEVER be discharged as an entry
/// assumption. Its public evidence-derived carrier remains canonical too.
#[test]
fn call_site_precondition_with_contract_id_is_never_entry_assumption_discharged() {
    let context = trust_verifier_api::ObligationContext::new(
        trust_verifier_api::ObligationProducer::CompilerMirExtract,
        trust_verifier_api::ObligationOrigin::VerificationCondition {
            vc_kind: "precondition".to_string(),
            vc_index: 0,
            formula_schema: None,
        },
    )
    .to_metadata_entry()
    .expect("obligation context serializes");
    let obligation = trust_verifier_api::TrustObligation {
        obligation_id: "vc:caller:precondition:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Precondition,
        // The same contract id as the callee's def-site marker — the exact
        // shape the reverted contract_id-based guard wrongly discharged.
        contract_id: Some("trust-contract:generate::Lcg::range_usize:requires:0".to_string()),
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "precondition of `generate::Lcg::range_usize`".to_string(),
        required_strength: Some(trust_verifier_api::ProofStrength::deductive()),
        summary_facts: Vec::new(),
        metadata: vec![context],
    };
    assert!(!is_definition_site_requires_marker(&obligation));

    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "bundle-callsite-precondition",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "generate".to_string(),
            path: "generate::caller".to_string(),
        },
    );
    bundle.obligations.push(obligation);
    let dispatched = full_verification_dispatched_obligations(
        &bundle,
        &ExactDefinitionEntryMarkerSet::default(),
    );
    assert_eq!(
        dispatched, bundle.obligations,
        "caller-side VerificationCondition preconditions must remain proof requests"
    );
    let evidence = unsupported_evidence_for(&bundle.obligations[0]);
    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("callsite-precondition-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        vec![evidence],
    );

    // Row path: stays a genuine (non-discharged) outcome — Unknown here.
    let (evidence_by_id, skipped_by_id) = index_run_result_obligations(&full_result);
    let strict_accepted_ids = strict_full_verification_accepted_obligation_ids(&full_result);
    let row_result = full_verification_legacy_result_for_obligation(
        &full_result.requested_obligations[0],
        &evidence_by_id,
        &skipped_by_id,
        &strict_accepted_ids,
        false,
        false,
    );
    assert!(
        matches!(row_result, VerificationResult::Unknown { .. }),
        "call-site precondition must stay genuinely proved/refuted, not entry-assumption discharged: {row_result:#?}"
    );

    full_result.validate_derived_state().expect("call-site public run stays canonical");
    full_result.try_to_manifest().expect("call-site public run stays manifestable");
}

/// Run the marker
/// through the REAL full native pipeline (bundle build -> native trust-ir
/// routing/binding -> `FullVerificationEngine::with_required_native_engines`
/// solve -> legacy results -> bridge -> transport). The compiler-private row is
/// discharged via `trust-entry-assumption`, while the sealed public catalog
/// retains the marker without routing it to a proof engine.
#[test]
fn def_site_requires_marker_keeps_public_and_private_carriers_in_parity() {
    let (function, compiler_contracts) = requires_marker_function();
    let (bundle, native_trust_ir_bundle, definition_entry_markers) =
        build_full_verification_input_for_tests_with_definition_entry_markers(
            &function,
            &compiler_contracts,
            &[],
        );
    let native_trust_ir_bundle =
        native_trust_ir_bundle.expect("native bundle build should not error");
    let engine = trust_router::FullVerificationEngine::with_required_native_engines();
    let context = trust_router::VerifierExecutionContext::new("requires-marker-verdict-test");
    let dispatched = full_verification_dispatched_obligations(&bundle, &definition_entry_markers);
    assert!(dispatched.iter().all(|obligation| {
        !is_definition_site_requires_marker(obligation) && obligation.is_default_admission()
    }));
    let full_result = verify_full_bundle_with_optional_native_trust_ir(
        &engine,
        &bundle,
        &dispatched,
        native_trust_ir_bundle.as_ref(),
        &context,
    );

    // The marker remains in the canonical catalog but is not a proof request:
    // proving a free `lo <= hi` would be semantically wrong at the callee.
    let marker = bundle
        .obligations
        .iter()
        .find(|obligation| is_definition_site_requires_marker(obligation))
        .expect("bundle must contain the def-site requires marker");
    assert!(
        !full_result
            .requested_obligations
            .iter()
            .any(|obligation| obligation.obligation_id == marker.obligation_id)
    );
    assert!(
        !full_result.evidence.iter().any(|evidence| evidence.obligation_id == marker.obligation_id)
    );

    // (1) Row/transport path.
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        panic!("function bundle subject")
    };
    let expected_function =
        trust_verifier_api::FunctionContext { crate_name: crate_name.clone(), path: path.clone() };
    let authority = CompilerFunctionAuthority::compatibility_for_test(expected_function);
    let snapshot = exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
        &function,
        &compiler_contracts,
        &bundle,
        &dispatched,
        &[],
        definition_entry_markers,
        &authority,
        context.snapshot(),
    );
    let (legacy_results, mut bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &full_result,
        &[],
        &snapshot,
    );
    let (results, _, _, _) =
        bridge_v1_ay_proofs_into_native_results(500, None, &[], &mut bindings, legacy_results);
    let cleancic = (0..results.len()).map(|_| None).collect::<Vec<_>>();
    let authorities =
        build_result_proof_authorities(&results, &bindings, Some(&full_result), &cleancic);
    let transport_rows = build_transport_results_with_runtime_checks_bound(
        true,
        None,
        &results,
        Some(&full_result),
        &cleancic,
        &bindings,
        &authorities,
    );
    let marker_index = transport_rows
        .iter()
        .position(|row| row.description.contains("requires contract"))
        .expect("marker transport row must exist");
    let marker_row = &transport_rows[marker_index];
    assert_eq!(marker_row.kind, "assumption:requires");
    assert_eq!(
        marker_row.outcome, Outcome::Skipped,
        "the transport boundary must expose the def-site requires marker as an assumption: {marker_row:#?}"
    );
    assert_eq!(marker_row.solver, TRUST_ENTRY_ASSUMPTION_SOLVER);
    assert!(matches!(
        authorities.get(marker_index).and_then(Option::as_ref),
        Some(ResultProofAuthority::DefinitionEntryAssumption { .. })
    ));
    let proof_results = build_proof_results_with_runtime_checks(
        true,
        &results,
        &[],
        &bindings,
        &authorities,
        Some(&function),
    );
    let marker_disposition =
        proof_results.dispositions.iter().nth(marker_index).expect("entry marker disposition");
    assert_eq!(marker_disposition.status, TrustStatus::Trusted);
    assert_eq!(marker_disposition.strength, TrustProofStrength::None);
    assert_eq!(marker_row.obligation_id.as_deref(), Some(marker.obligation_id.as_str()));
    assert!(marker_row.claim_digest_sha256.is_some());
    assert_eq!(marker_row.reason.as_deref(), Some(TRUST_ENTRY_ASSUMPTION_REASON));
    assert!(
        marker_row.proof_evidence.is_none(),
        "a definition-entry assumption may close modular bookkeeping, but must carry no proof metadata"
    );

    assert_eq!(
        full_verification_failure(
            &proof_results.summary,
            &transport_rows,
            &results,
            &bindings,
            &authorities,
        ),
        None,
        "an authenticated catalog assumption is not a skipped proof obligation",
    );
    assert_eq!(
        strict_l0_verification_failure(true, &results, &bindings, &authorities, Some(&full_result),),
        None,
        "the authenticated entry marker must be excluded before UnsupportedMir is classified L0",
    );

    let no_authorities = vec![None; authorities.len()];
    assert_eq!(
        full_verification_failure(
            &proof_results.summary,
            &transport_rows,
            &results,
            &bindings,
            &no_authorities,
        ),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 }),
        "public assumption transport strings cannot suppress strict accounting",
    );
    assert_eq!(
        strict_l0_verification_failure(
            true,
            &results,
            &bindings,
            &no_authorities,
            Some(&full_result),
        ),
        Some(FullVerificationFailure { failed: 0, unknown: 1, runtime_checked: 0, skipped: 0 }),
        "the same UnsupportedMir row and entry solver label remain fatal without private authority",
    );

    let mut ordinary_skipped = marker_row.clone();
    ordinary_skipped.obligation_id = Some("ordinary-skipped-obligation".to_string());
    ordinary_skipped.kind = "slice".to_string();
    ordinary_skipped.solver = "ordinary-backend".to_string();
    ordinary_skipped.reason = Some("ordinary backend skip".to_string());
    let moved_rows = vec![ordinary_skipped, marker_row.clone()];
    assert_eq!(
        full_verification_failure(
            &proof_results.summary,
            &moved_rows,
            &results,
            &bindings,
            &authorities,
        ),
        Some(FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 2 }),
        "a moved transport row cannot borrow a neighboring entry-assumption capability",
    );

    assert_eq!(full_result.status, trust_verifier_api::VerificationRunStatus::Empty);
    assert_eq!(full_result.summary.requested_obligations, 0);
    assert_eq!(full_result.summary.unsupported, 0);
    full_result.validate_derived_state().expect("public entry-marker run stays canonical");
    full_result.try_to_manifest().expect("public entry-marker run stays manifestable");
}

/// Regression pin for the vacuity-gate verdict path (`build_proof_results`):
/// the entry-assumption discharge rides the marker's deliberate `Bool(false)`
/// bookkeeping placeholder VC, so the phase-A vacuity gate used to re-downgrade
/// it to Unknown — resurrecting the "every contracted function is unknown"
/// verdict through `proof_results.summary`. Only the private, origin-checked
/// authority is exempt; a forgeable solver/backend name is not.
#[test]
fn entry_assumption_vacuity_exemption_requires_private_authority() {
    let (function, compiler_contracts) = requires_marker_function();
    let bundle =
        trust_mir_extract::function_to_verifier_api_bundle(&function, &compiler_contracts, &[]);
    let marker = bundle
        .obligations
        .iter()
        .find(|obligation| is_definition_site_requires_marker(obligation))
        .expect("bundle must contain the def-site requires marker");
    let marker_vc = legacy_vc_from_api_obligation(&function, marker);
    assert!(
        matches!(marker_vc.formula, trust_types::Formula::Bool(false)),
        "the marker's legacy VC is the Bool(false) bookkeeping placeholder"
    );

    let entry_assumption = VerificationResult::Proved {
        // Attribution is deliberately different: authority, not this string,
        // licenses the modular entry-assumption representation.
        solver: trust_types::Symbol::intern("entry-attribution-is-not-authority"),
        time_ms: 0,
        strength: trust_types::ProofStrength::deductive(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let entry_binding =
        result_obligation_binding_with_compiler_assumptions(0, &marker_vc, marker, true, false)
            .expect("entry marker binding");
    let entry_authority = ResultProofAuthority::DefinitionEntryAssumption {
        row: exact_result_row_identity(0, &marker_vc).expect("serializable marker row"),
        binding: entry_binding.clone(),
    };
    assert_eq!(
        trust_disposition_for_authority(
            Some(&entry_authority),
            0,
            &marker_vc,
            &entry_assumption,
            Some(&entry_binding),
        ),
        Some((TrustStatus::Trusted, TrustProofStrength::None)),
        "entry assumptions use the contract-assumed bucket without invented proof strength"
    );
    assert!(!entry_authority.is_static_proof_for(
        0,
        &marker_vc,
        &entry_assumption,
        Some(&entry_binding),
    ));
    assert!(!entry_authority.permits_static_proved_transport_for(
        0,
        &marker_vc,
        &entry_assumption,
        Some(&entry_binding),
    ));
    let gated = apply_vacuity_gate_with_authority(
        0,
        &marker_vc,
        entry_assumption.clone(),
        Some(&entry_binding),
        Some(&entry_authority),
    );
    assert!(
        matches!(gated, VerificationResult::Proved { .. }),
        "the entry-assumption discharge must survive the vacuity gate: {gated:#?}"
    );

    let full_result = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("duplicate-entry-authority-test").snapshot(),
        &bundle,
        trust_verifier_api::EngineManifest::new(
            "trust-full-verifier",
            trust_verifier_api::API_VERSION,
            trust_verifier_api::EngineKind::Composite,
        ),
        &bundle.obligations,
        vec![unsupported_evidence_for(marker)],
    );
    let duplicate_results = vec![
        (marker_vc.clone(), entry_assumption.clone()),
        (marker_vc.clone(), entry_assumption.clone()),
    ];
    let duplicate_bindings = vec![Some(entry_binding.clone()), Some(entry_binding.clone())];
    let duplicate_kernel_evidence = vec![None, None];
    let duplicate_authorities = build_result_proof_authorities(
        &duplicate_results,
        &duplicate_bindings,
        Some(&full_result),
        &duplicate_kernel_evidence,
    );
    assert!(
        duplicate_authorities.iter().all(Option::is_none),
        "duplicate exact rows must fail before private entry-assumption authority is minted",
    );
    let duplicate_transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &duplicate_results,
        Some(&full_result),
        &duplicate_kernel_evidence,
        &duplicate_bindings,
        &duplicate_authorities,
    );
    assert!(
        duplicate_transport.iter().all(|row| row.outcome == Outcome::Unknown
            && row.reason.as_deref().is_some_and(|reason| reason.contains("without exact"))),
        "transport must share the authority-minting cardinality gate: {duplicate_transport:#?}",
    );

    // An API engine may choose the former sentinel as its public name. Without
    // the private variant, that exact string still receives no exemption.
    let forged_name = VerificationResult::Proved {
        solver: trust_types::Symbol::intern(TRUST_ENTRY_ASSUMPTION_SOLVER),
        time_ms: 0,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    assert!(is_entry_assumption_discharge(&forged_name));
    let gated_solver = apply_vacuity_gate_with_authority(0, &marker_vc, forged_name, None, None);
    assert!(
        matches!(gated_solver, VerificationResult::Unknown { .. }),
        "a solver proof of a constant-false goal must still be vacuity-rejected: {gated_solver:#?}"
    );

    // Nor may a fake/indexed CleanCic bit turn the non-semantic placeholder
    // into a private kernel token.
    let public_proved = VerificationResult::Proved {
        solver: trust_types::Symbol::intern("solver"),
        time_ms: 0,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let authorities = build_result_proof_authorities(
        &[(marker_vc, public_proved)],
        &[],
        None,
        &[Some(authority_test_clean_cic(91))],
    );
    assert!(authorities.iter().all(Option::is_none));
}

#[test]
fn entry_assumption_never_authorizes_unconditional_panic_freedom() {
    let proved = |solver: &str| VerificationResult::Proved {
        solver: trust_types::Symbol::intern(solver),
        time_ms: 0,
        strength: trust_types::ProofStrength::deductive(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let unconditional = vec![(test_vc(1), proved("clean-kernel-certified"))];
    let unconditional_authority = vec![Some(ResultProofAuthority::KernelCertified {
        row: exact_result_row_identity(0, &unconditional[0].0).expect("serializable kernel row"),
        evidence: authority_test_clean_cic(70),
    })];
    assert!(results_establish_unconditional_panic_freedom(
        &unconditional,
        &[],
        &unconditional_authority,
    ));

    let conditional = vec![
        (test_vc(1), proved("clean-kernel-certified")),
        (test_vc(2), proved(TRUST_ENTRY_ASSUMPTION_SOLVER)),
    ];
    let entry_binding = result_obligation_binding_with_compiler_assumptions(
        1,
        &conditional[1].0,
        &authority_test_native_obligation("authority:entry-assumption", 72, 2),
        true,
        false,
    )
    .expect("entry binding");
    let conditional_bindings = vec![None, Some(entry_binding.clone())];
    assert!(
        !results_establish_unconditional_panic_freedom(
            &conditional,
            &conditional_bindings,
            &[
                Some(ResultProofAuthority::KernelCertified {
                    row: exact_result_row_identity(0, &conditional[0].0)
                        .expect("serializable kernel row"),
                    evidence: authority_test_clean_cic(71),
                }),
                Some(ResultProofAuthority::DefinitionEntryAssumption {
                    row: exact_result_row_identity(1, &conditional[1].0)
                        .expect("serializable entry row"),
                    binding: entry_binding,
                }),
            ],
        ),
        "a body proved under `requires` is not panic-free for all inputs"
    );

    assert!(
        !all_results_have_static_proof_authority(
            &conditional,
            &conditional_bindings,
            &[None, None],
        ),
        "raw Proved labels alone must not satisfy an all-results proof gate"
    );
    assert!(all_results_have_static_proof_authority(&[], &[], &[]));

    assert!(!results_establish_unconditional_panic_freedom(&[], &[], &[]));
}

#[test]
fn contract_assumed_disposition_cannot_seed_dynamic_static_summary() {
    let mut dispositions = IndexVec::new();
    dispositions.push(TrustDisposition {
        kind: TrustObligationKind::Precondition,
        status: TrustStatus::Trusted,
        strength: TrustProofStrength::None,
        certified: false,
    });
    let mut fingerprints = IndexVec::new();
    fingerprints.push(rustc_data_structures::fingerprint::Fingerprint::ZERO);
    let summary = TrustFunctionSummary::from_dispositions(&dispositions);
    let proof_results = TrustProofResults { dispositions, fingerprints, summary };
    assert!(proof_results.is_fully_verified(), "modular contract result remains valid");
    assert!(
        !has_nonzero_accounted_static_proof(&proof_results),
        "contract-assumed bookkeeping must not become a dynamic-dispatch proof summary"
    );
}

#[test]
fn extern_abi_non_unwinding_whitelist_is_airtight() {
    // SOUNDNESS: an absent callee's panic-freedom is discharged ONLY when its ABI
    // is a non-unwinding C-family boundary (a cross-boundary unwind aborts, never
    // reaching the caller). Everything that CAN unwind must return false so it
    // stays fail-closed.
    use rustc_abi::ExternAbi::*;
    for abi in [
        C { unwind: false },
        System { unwind: false },
        Cdecl { unwind: false },
        Stdcall { unwind: false },
        Fastcall { unwind: false },
        Thiscall { unwind: false },
        Vectorcall { unwind: false },
        Aapcs { unwind: false },
        SysV64 { unwind: false },
        Win64 { unwind: false },
    ] {
        assert!(super::extern_abi_is_non_unwinding(abi), "{abi:?} must be non-unwinding");
    }
    for abi in [
        C { unwind: true },
        System { unwind: true },
        Cdecl { unwind: true },
        Win64 { unwind: true },
        Rust,
        RustCall,
        RustCold,
    ] {
        assert!(!super::extern_abi_is_non_unwinding(abi), "{abi:?} is not a non-unwind boundary");
    }
}

#[test]
fn bodyless_nonunwind_foreign_call_requires_an_exact_registered_proof() {
    let mut function = native_trust_ir_panic_function(false);
    let callee = "ffi::bodyless_nonunwind";
    let trust_types::Terminator::Call { func, is_foreign, target, .. } =
        &mut function.body.blocks[1].terminator
    else {
        panic!("fixture call terminator");
    };
    *func = callee.to_string();
    *is_foreign = true;
    *target = Some(trust_types::BlockId(2));

    let mut proven = FxHashSet::default();
    assert!(
        !all_calls_target_proven_panic_free_in_set(&proven, &function),
        "bodyless/foreign/non-unwind classification must not be proof authority"
    );
    proven.insert(callee.to_string());
    assert!(
        all_calls_target_proven_panic_free_in_set(&proven, &function),
        "only an exact registered proof may satisfy the interprocedural gate"
    );
}

#[test]
fn mutual_scc_oracle_excludes_self_recursion_and_finds_full_components() {
    // 0 -> 0 is a safe direct self-loop. 1 <-> 2 and 3 -> 4 -> 5 -> 3
    // are the two mutual SCCs; 6 is an acyclic sink.
    let adjacency = vec![vec![0], vec![2], vec![1], vec![4], vec![5], vec![3], vec![]];
    assert_eq!(mutually_recursive_node_indices(&adjacency), vec![1, 2, 3, 4, 5]);
}

#[test]
fn mutual_scc_oracle_is_linear_and_stack_safe_on_a_long_acyclic_chain() {
    const NODE_COUNT: usize = 20_000;
    let mut adjacency = vec![Vec::new(); NODE_COUNT];
    for (node, successors) in adjacency.iter_mut().enumerate().take(NODE_COUNT - 1) {
        successors.push(node + 1);
    }
    assert!(mutually_recursive_node_indices(&adjacency).is_empty());
}

#[test]
fn certified_monitor_uses_canonical_compiler_predicate_body() {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind, TrustContractProposition,
        TrustContractPropositionDomain as Domain,
    };

    rustc_span::create_default_session_globals_then(|| {
        assert_eq!(
            canonical_monitor_opaque_predicate_text(
                "__trust_lowered_compiler_contract__:(x) == (result)",
            )
            .as_deref(),
            Ok("(x) == (result)")
        );
        let lowered = TrustContractPredicateKind::Typed {
            text: Symbol::intern("__trust_lowered_compiler_contract__:(x) == (result)"),
            proposition: TrustContractProposition::Eq(
                Box::new(TrustContractProposition::Var {
                    name: Symbol::intern("x"),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }),
                Box::new(TrustContractProposition::Var {
                    name: Symbol::intern("_0"),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }),
            ),
        };
        assert_eq!(canonical_monitor_predicate_text(&lowered).as_deref(), Ok("(x) == (result)"));
        assert_eq!(
            canonical_monitor_static_proposition(&lowered),
            Ok(StaticMonitorProposition {
                formula: Formula::Eq(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                ),
                variable_domains: vec![
                    trust_types::CompilerContractVariableDomain {
                        name: "_0".to_string(),
                        domain: trust_types::CompilerContractValueDomain::MachineInt {
                            width: 8,
                            signed: false,
                        },
                    },
                    trust_types::CompilerContractVariableDomain {
                        name: "x".to_string(),
                        domain: trust_types::CompilerContractValueDomain::MachineInt {
                            width: 8,
                            signed: false,
                        },
                    },
                ],
            })
        );
        let missing_prefix = TrustContractPredicateKind::Typed {
            text: Symbol::intern("(x) == (result)"),
            proposition: TrustContractProposition::Eq(
                Box::new(TrustContractProposition::Var {
                    name: Symbol::intern("x"),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }),
                Box::new(TrustContractProposition::Var {
                    name: Symbol::intern("_0"),
                    domain: Domain::MachineInt { width: 8, signed: false },
                }),
            ),
        };
        assert!(canonical_monitor_static_proposition(&missing_prefix).is_err());

        let mir_local = TrustContractPredicateKind::MirLocal { local: Local::arg(0) };
        assert!(canonical_monitor_predicate_text(&mir_local).is_err());
        let literal = TrustContractPredicateKind::BoolLiteral { value: true };
        assert!(canonical_monitor_predicate_text(&literal).is_err());
    });
}

#[test]
fn resolved_scalar_carriers_preserve_broad_elaboration_and_narrow_runtime_policy() {
    for (carrier, name, runtime) in [
        (TrustResolvedScalarType::U8, "u8", true),
        (TrustResolvedScalarType::U16, "u16", true),
        (TrustResolvedScalarType::U32, "u32", true),
        (TrustResolvedScalarType::U64, "u64", true),
        (TrustResolvedScalarType::Usize, "usize", false),
        (TrustResolvedScalarType::I8, "i8", false),
        (TrustResolvedScalarType::I16, "i16", false),
        (TrustResolvedScalarType::I32, "i32", false),
        (TrustResolvedScalarType::I64, "i64", false),
        (TrustResolvedScalarType::Isize, "isize", false),
        (TrustResolvedScalarType::Bool, "bool", true),
    ] {
        assert_eq!(carrier.elaborator_name(), name);
        assert_eq!(carrier.supports_runtime_monitor(), runtime);
    }
}

#[test]
fn certified_monitor_rejects_nonexact_runtime_domains() {
    use trust_types::{CompilerContractValueDomain as Domain, CompilerContractVariableDomain};

    let runtime = trust_spec_elab::certify_monitor_from_typed_scope("x == 0", &[("x", "u8")])
        .expect("u8 equality certifies")
        .into_runtime();
    let binding = |domain| vec![CompilerContractVariableDomain { name: "x".to_string(), domain }];
    assert!(
        validate_runtime_monitor_domains(
            &runtime,
            &binding(Domain::MachineInt { width: 8, signed: false })
        )
        .is_ok()
    );
    for wrong in [
        Domain::MachineInt { width: 16, signed: false },
        Domain::MachineInt { width: 128, signed: false },
        Domain::MachineInt { width: 8, signed: true },
        Domain::PointerSizedInt { width: 8, signed: false },
        Domain::Bool,
        Domain::MathematicalInt,
    ] {
        assert!(validate_runtime_monitor_domains(&runtime, &binding(wrong)).is_err());
    }
    assert!(validate_runtime_monitor_domains(&runtime, &[]).is_err());
    assert!(
        validate_runtime_monitor_domains(
            &runtime,
            &[
                CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: Domain::MachineInt { width: 8, signed: false },
                },
                CompilerContractVariableDomain {
                    name: "z".to_string(),
                    domain: Domain::MachineInt { width: 8, signed: false },
                },
            ]
        )
        .is_err()
    );

    let nat = trust_spec_elab::certify_monitor_from_typed_scope("x == 0", &[("x", "nat")])
        .expect("logical Nat monitor certifies")
        .into_runtime();
    assert!(validate_runtime_monitor_domains(&nat, &binding(Domain::MathematicalInt)).is_err());
}

fn zero_eq_bound_monitor() -> BoundCertifiedMonitor {
    let static_formula = Formula::Eq(Box::new(Formula::Int(0)), Box::new(Formula::Int(0)));
    let certified = trust_spec_elab::certify_monitor_from_typed_scope("0 == 0", &[])
        .expect("closed equality certifies");
    bind_certified_monitor_to_static_formula(
        certified,
        StaticMonitorProposition { formula: static_formula, variable_domains: Vec::new() },
    )
    .expect("closed certified monitor binds to its exact static tree")
}

fn zero_eq_typed_proposition_digest() -> String {
    let bound = zero_eq_bound_monitor();
    trust_types::typed_contract_proposition_digest(&bound.static_formula, &bound.variable_domains)
}

fn u8_wrapping_bound_monitor() -> BoundCertifiedMonitor {
    use trust_types::{CompilerContractValueDomain, CompilerContractVariableDomain};

    let certified = trust_spec_elab::certify_monitor_from_typed_scope(
        "x + y == 0",
        &[("x", "u8"), ("y", "u8")],
    )
    .expect("the Clean kernel should certify exact u8 wrapping evaluation");
    bind_certified_monitor_to_static_formula(
        certified,
        StaticMonitorProposition {
            formula: Formula::Eq(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Var("y".to_string(), Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            ),
            variable_domains: vec![
                CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: CompilerContractValueDomain::MachineInt { width: 8, signed: false },
                },
                CompilerContractVariableDomain {
                    name: "y".to_string(),
                    domain: CompilerContractValueDomain::MachineInt { width: 8, signed: false },
                },
            ],
        },
    )
    .expect("the certified runtime tree must bind to the exact typed static proposition")
}

#[test]
fn certified_monitor_static_binding_rejects_structural_drift() {
    let certified = trust_spec_elab::certify_monitor_from_typed_scope("0 == 0", &[])
        .expect("closed equality certifies");
    assert!(
        bind_certified_monitor_to_static_formula(
            certified,
            StaticMonitorProposition {
                formula: Formula::Eq(Box::new(Formula::Int(0)), Box::new(Formula::Int(0)),),
                variable_domains: Vec::new(),
            },
        )
        .is_ok()
    );
    let drifted = trust_spec_elab::certify_monitor_from_typed_scope("0 == 0", &[])
        .expect("closed equality certifies");
    assert!(
        bind_certified_monitor_to_static_formula(
            drifted,
            StaticMonitorProposition {
                formula: Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Int(0)),),
                variable_domains: Vec::new(),
            },
        )
        .expect_err("operator drift must fail closed")
        .contains("differs structurally")
    );
}

#[test]
fn certified_monitor_static_binding_supports_mixed_bool_unsigned_atoms() {
    use trust_types::{CompilerContractValueDomain as Domain, CompilerContractVariableDomain};

    let certified = trust_spec_elab::certify_monitor_from_typed_scope(
        "flag && x + 1 < 10",
        &[("flag", "bool"), ("x", "u8")],
    )
    .expect("mixed Bool/u8 arithmetic monitor certifies per atom");
    let bound = bind_certified_monitor_to_static_formula(
        certified,
        StaticMonitorProposition {
            formula: Formula::And(vec![
                Formula::Var("flag".to_string(), Sort::Bool),
                Formula::Lt(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("x".to_string(), Sort::Int)),
                        Box::new(Formula::Int(1)),
                    )),
                    Box::new(Formula::UInt(10)),
                ),
            ]),
            variable_domains: vec![
                CompilerContractVariableDomain { name: "flag".to_string(), domain: Domain::Bool },
                CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: Domain::MachineInt { width: 8, signed: false },
                },
            ],
        },
    )
    .expect("static and certified trees/domains must match exactly");
    assert!(bound.runtime.evaluate(&[("flag", 1), ("x", 255)]).unwrap());
    assert!(!bound.runtime.evaluate(&[("flag", 0), ("x", 255)]).unwrap());
}

#[test]
fn certified_monitor_static_binding_maps_result_to_return_place_name() {
    use trust_types::{CompilerContractValueDomain as Domain, CompilerContractVariableDomain};

    let certified =
        trust_spec_elab::certify_monitor_from_typed_scope("result == true", &[("result", "bool")])
            .expect("Bool result equality certifies");
    bind_certified_monitor_to_static_formula(
        certified,
        StaticMonitorProposition {
            formula: Formula::Eq(
                Box::new(Formula::Var("_0".to_string(), Sort::Bool)),
                Box::new(Formula::Bool(true)),
            ),
            variable_domains: vec![CompilerContractVariableDomain {
                name: "_0".to_string(),
                domain: Domain::Bool,
            }],
        },
    )
    .expect("result must bind exactly to static `_0`");
}

#[test]
fn static_monitor_projector_admits_exact_literals_and_safe_arithmetic_only() {
    use trust_types::{CompilerContractValueDomain as Domain, CompilerContractVariableDomain};

    let sidecar = vec![CompilerContractVariableDomain {
        name: "x".to_string(),
        domain: Domain::MachineInt { width: 64, signed: false },
    }];
    let x = || Formula::Var("x".to_string(), Sort::Int);
    for formula in [
        Formula::Eq(
            Box::new(Formula::Sub(Box::new(x()), Box::new(Formula::Int(1)))),
            Box::new(Formula::UInt(2)),
        ),
        Formula::Eq(
            Box::new(Formula::Div(Box::new(x()), Box::new(Formula::UInt(2)))),
            Box::new(Formula::Int(1)),
        ),
        Formula::Eq(
            Box::new(Formula::Rem(Box::new(x()), Box::new(Formula::Int(2)))),
            Box::new(Formula::UInt(1)),
        ),
    ] {
        assert!(static_formula_monitor_expr(&formula, &sidecar).is_ok(), "{formula:?}");
    }

    for formula in [
        Formula::Eq(Box::new(Formula::Int(-1)), Box::new(Formula::Int(0))),
        Formula::Eq(Box::new(Formula::UInt(u128::from(u64::MAX) + 1)), Box::new(Formula::Int(0))),
        Formula::Eq(
            Box::new(Formula::Div(Box::new(x()), Box::new(Formula::Int(0)))),
            Box::new(Formula::Int(0)),
        ),
        Formula::Eq(
            Box::new(Formula::Rem(Box::new(x()), Box::new(x()))),
            Box::new(Formula::Int(0)),
        ),
    ] {
        assert!(static_formula_monitor_expr(&formula, &sidecar).is_err(), "{formula:?}");
    }

    // With no variable/domain sidecar, the static proposition is
    // mathematical Int while Clean would default the executable term to
    // truncating Nat subtraction. The two meanings must never bind.
    let closed_subtraction = Formula::Eq(
        Box::new(Formula::Sub(Box::new(Formula::Int(0)), Box::new(Formula::Int(1)))),
        Box::new(Formula::Int(0)),
    );
    assert!(
        static_formula_monitor_expr(&closed_subtraction, &[])
            .expect_err("closed Int subtraction must not borrow Nat semantics")
            .contains("no exact Nat runtime monitor")
    );
}

#[test]
fn certified_monitor_rejects_closed_nat_evaluation_outside_exact_runtime_representation() {
    let max = u64::MAX;
    let text = format!("({max} * {max}) + ({max} * {max}) == 0");
    let certified = trust_spec_elab::certify_monitor_from_typed_scope(&text, &[])
        .expect("the Clean kernel can certify the closed Nat decision procedure");
    let formula = trust_types::parse_spec_expr(&text).expect("static proposition parses");
    let error = bind_certified_monitor_to_static_formula(
        certified,
        StaticMonitorProposition { formula, variable_domains: Vec::new() },
    )
    .expect_err("a closed monitor that cannot be evaluated exactly must stay unmonitored");
    assert!(
        error.contains("closed certified monitor is not exactly executable"),
        "unexpected rejection: {error}"
    );
}

#[test]
fn certified_monitor_public_metadata_keys_are_stable() {
    assert_eq!(TRUST_MONITOR_STATUS_METADATA_KEY, "trust.monitor.status");
    assert_eq!(TRUST_MONITOR_REASON_METADATA_KEY, "trust.monitor.reason");
    assert_eq!(TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY, "trust.monitor.predicate_digest");
}

#[test]
fn public_monitor_digest_serialization_failure_has_no_identity_fallback() {
    let error = public_monitor_digest_from_payload(
        "trust.monitor.test.v1",
        Err("synthetic serialization failure".to_string()),
    )
    .expect_err("serialization failure must make the monitor digest unavailable");

    assert_eq!(error, "synthetic serialization failure");
    assert_eq!(TRUST_MONITOR_DIGEST_UNAVAILABLE, "unavailable");

    let mut metadata = Vec::new();
    stamp_unmatched_public_monitor_metadata(
        &mut metadata,
        "no kernel-certified monitor evidence matched this test row",
        Err(error),
    );
    assert!(metadata.iter().any(|entry| {
        entry.key == TRUST_MONITOR_STATUS_METADATA_KEY && entry.value == "unmonitored"
    }));
    assert!(metadata.iter().any(|entry| {
        entry.key == TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY
            && entry.value == TRUST_MONITOR_DIGEST_UNAVAILABLE
    }));
    assert!(metadata.iter().any(|entry| {
        entry.key == TRUST_MONITOR_REASON_METADATA_KEY
            && entry.value.contains("monitor predicate digest unavailable")
    }));
    assert!(
        transport_monitor_evidence_from_metadata(&metadata).is_none(),
        "an unavailable digest must never become transport monitor evidence"
    );
}

#[test]
fn certified_monitor_transport_metadata_parser_is_strict_and_fail_closed() {
    let metadata = |status: &str, reason: &str, digest: &str| {
        vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_STATUS_METADATA_KEY.to_string(),
                value: status.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_REASON_METADATA_KEY.to_string(),
                value: reason.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: digest.to_string(),
            },
        ]
    };
    let monitored_digest = format!("sha256:{}", "a".repeat(64));
    let unmonitored_digest = format!("sha256:{}", "b".repeat(64));
    let monitored = metadata("monitored", "Clean kernel accepted equivalence", &monitored_digest);
    let unmonitored = metadata(
        "unmonitored",
        "quantified proposition has no finite monitor",
        &unmonitored_digest,
    );
    assert_eq!(
        transport_monitor_evidence_from_metadata(&monitored),
        Some(trust_types::TransportMonitorEvidence {
            status: trust_types::TransportMonitorStatus::Monitored,
            reason: "Clean kernel accepted equivalence".to_string(),
            predicate_digest: monitored_digest,
        })
    );
    assert_eq!(
        transport_monitor_evidence_from_metadata(&unmonitored),
        Some(trust_types::TransportMonitorEvidence {
            status: trust_types::TransportMonitorStatus::Unmonitored,
            reason: "quantified proposition has no finite monitor".to_string(),
            predicate_digest: unmonitored_digest,
        })
    );

    for invalid in [
        metadata("assumed", "forged status", &format!("sha256:{}", "c".repeat(64))),
        metadata("monitored", "", &format!("sha256:{}", "d".repeat(64))),
        metadata("monitored", "   ", &format!("sha256:{}", "e".repeat(64))),
        metadata(
            "monitored",
            &"x".repeat(TRUST_MONITOR_REASON_MAX_BYTES + 1),
            &format!("sha256:{}", "f".repeat(64)),
        ),
        metadata("monitored", "bad digest", &format!("sha256:{}", "A".repeat(64))),
        metadata("monitored", "bad digest", &format!("sha256:{}", "0".repeat(63))),
        metadata("monitored", "bad digest", &"0".repeat(64)),
    ] {
        assert!(
            transport_monitor_evidence_from_metadata(&invalid).is_none(),
            "malformed monitor metadata must never create transport evidence",
        );
    }

    for duplicate_key in [
        TRUST_MONITOR_STATUS_METADATA_KEY,
        TRUST_MONITOR_REASON_METADATA_KEY,
        TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY,
    ] {
        let mut duplicated = monitored.clone();
        let value = duplicated
            .iter()
            .find(|entry| entry.key == duplicate_key)
            .expect("fixture metadata key")
            .value
            .clone();
        duplicated
            .push(trust_verifier_api::MetadataEntry { key: duplicate_key.to_string(), value });
        assert!(
            transport_monitor_evidence_from_metadata(&duplicated).is_none(),
            "duplicate `{duplicate_key}` must fail closed",
        );
    }
}

#[test]
fn certified_monitor_metadata_is_dense_indexed_complete_and_utf8_bounded() {
    let subject = trust_verifier_api::BundleSubject::Function {
        crate_name: "monitor_metadata".to_string(),
        path: "monitor_metadata::f".to_string(),
    };
    let mut bundle = trust_verifier_api::TrustContractBundle::empty("monitor-bundle", subject);

    let stale_monitor_metadata = || {
        vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_STATUS_METADATA_KEY.to_string(),
                value: "stale".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_STATUS_METADATA_KEY.to_string(),
                value: "duplicate".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_REASON_METADATA_KEY.to_string(),
                value: "stale".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: "sha256:stale".to_string(),
            },
        ]
    };
    let contract =
        |index: usize, digest: char, kind: trust_verifier_api::ContractKind, kind_label: &str| {
            let mut metadata = stale_monitor_metadata();
            metadata.push(trust_verifier_api::MetadataEntry {
                key: "trust.contract.kind".to_string(),
                value: kind_label.to_string(),
            });
            metadata.push(trust_verifier_api::MetadataEntry {
                key: "trust.contract.lowering".to_string(),
                value: "typed_formula_v1".to_string(),
            });
            metadata.push(trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: "d".repeat(64),
            });
            metadata.push(trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: digest.to_string().repeat(64),
            });
            metadata.push(trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: zero_eq_typed_proposition_digest(),
            });
            trust_verifier_api::TrustContract {
                contract_id: format!("trust-contract:monitor_metadata::f:{kind_label}:{index}"),
                kind,
                predicate: trust_verifier_api::ContractPredicate::TrustExpr {
                    text: format!("predicate_{index}"),
                },
                source: trust_verifier_api::SourceLocation::default(),
                metadata,
            }
        };

    // Deliberately not source-index order: metadata must follow the dense id,
    // never the public vector position.
    bundle.contracts = vec![
        contract(2, 'c', trust_verifier_api::ContractKind::Requires, "requires"),
        contract(0, 'a', trust_verifier_api::ContractKind::Requires, "requires"),
        contract(1, 'b', trust_verifier_api::ContractKind::Ensures, "ensures"),
    ];
    let contract_ids = bundle
        .contracts
        .iter()
        .map(|contract| contract.contract_id.clone())
        .collect::<std::collections::BTreeSet<_>>();

    let obligation = |index: usize,
                      contract_id: String,
                      digest: char,
                      kind: trust_verifier_api::ObligationKind,
                      kind_label: &str| {
        let mut metadata = stale_monitor_metadata();
        let contract_kind = match kind_label {
            "requires" => trust_verifier_api::ContractKind::Requires,
            "ensures" => trust_verifier_api::ContractKind::Ensures,
            _ => panic!("fixture uses only requires/ensures rows"),
        };
        metadata.push(
            trust_verifier_api::ObligationContext::new(
                trust_verifier_api::ObligationProducer::CompilerMirExtract,
                trust_verifier_api::ObligationOrigin::Contract {
                    contract_id: contract_id.clone(),
                    contract_kind,
                    contract_index: index,
                    predicate_schema: None,
                },
            )
            .with_function(trust_verifier_api::FunctionContext {
                crate_name: "monitor_metadata".to_string(),
                path: "monitor_metadata::f".to_string(),
            })
            .to_metadata_entry()
            .expect("fixture context serializes"),
        );
        metadata.push(trust_verifier_api::MetadataEntry {
            key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
            value: "d".repeat(64),
        });
        metadata.push(trust_verifier_api::MetadataEntry {
            key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
            value: digest.to_string().repeat(64),
        });
        metadata.push(trust_verifier_api::MetadataEntry {
            key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
            value: zero_eq_typed_proposition_digest(),
        });
        let obligation_kind_label = match kind {
            trust_verifier_api::ObligationKind::Precondition => "precondition",
            trust_verifier_api::ObligationKind::Postcondition => "postcondition",
            _ => panic!("fixture uses only requires/ensures rows"),
        };
        trust_verifier_api::TrustObligation {
            obligation_id: format!(
                "obligation:monitor_metadata__f:{obligation_kind_label}:{index}"
            ),
            kind,
            contract_id: Some(contract_id),
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation::default(),
            description: format!("prove {kind_label} contract"),
            required_strength: Some(trust_verifier_api::ProofStrength::deductive()),
            summary_facts: Vec::new(),
            metadata,
        }
    };
    let id_for = |index: usize| {
        bundle
            .contracts
            .iter()
            .find(|contract| monitor_contract_source_index(&contract.contract_id) == Some(index))
            .map(|contract| contract.contract_id.clone())
            .expect("contract id by dense index")
    };
    bundle.obligations = vec![
        obligation(1, id_for(1), 'b', trust_verifier_api::ObligationKind::Postcondition, "ensures"),
        obligation(0, id_for(0), 'a', trust_verifier_api::ObligationKind::Precondition, "requires"),
        obligation(2, id_for(2), 'c', trust_verifier_api::ObligationKind::Precondition, "requires"),
    ];
    let mut reference = bundle.clone();
    for contract in &mut reference.contracts {
        contract.metadata = monitor_metadata_stripped(&contract.metadata);
    }
    for obligation in &mut reference.obligations {
        obligation.metadata = monitor_metadata_stripped(&obligation.metadata);
    }

    let mut mismatched_obligation =
        obligation(0, id_for(0), 'd', trust_verifier_api::ObligationKind::Precondition, "requires");
    mismatched_obligation.description = "mismatched public predicate digest".to_string();
    let mut unsupported_fallback = mismatched_obligation.clone();
    unsupported_fallback.obligation_id = "unsupported:monitor_metadata__f:3".to_string();
    unsupported_fallback.contract_id = None;
    unsupported_fallback.description = "derived contract obligation 3".to_string();
    unsupported_fallback.metadata.push(trust_verifier_api::MetadataEntry {
        key: "trust.contract.kind".to_string(),
        value: "requires".to_string(),
    });
    unsupported_fallback
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
        .expect("fixture predicate digest")
        .value = "e".repeat(64);
    bundle.obligations.insert(1, unsupported_fallback);
    bundle.obligations.push(mismatched_obligation);

    let long_utf8_reason = "é".repeat(TRUST_MONITOR_REASON_MAX_BYTES);
    let records = vec![
        ClauseMonitorRecord {
            source_index: 0,
            kind: rustc_middle::mir::trust_contract::TrustContractKind::Requires,
            span: DUMMY_SP,
            predicate_digest: format!("sha256:{}", "a".repeat(64)),
            typed_proposition_digest: Some(zero_eq_typed_proposition_digest()),
            evidence: ClauseMonitorEvidence::Monitored(zero_eq_bound_monitor()),
        },
        ClauseMonitorRecord {
            source_index: 1,
            kind: rustc_middle::mir::trust_contract::TrustContractKind::Ensures,
            span: DUMMY_SP,
            predicate_digest: format!("sha256:{}", "b".repeat(64)),
            typed_proposition_digest: None,
            evidence: ClauseMonitorEvidence::Unmonitored { reason: long_utf8_reason },
        },
        // Dense index alone is insufficient: this wrong-kind record must not
        // stamp the Requires contract/obligation at index 2 as monitored.
        ClauseMonitorRecord {
            source_index: 2,
            kind: rustc_middle::mir::trust_contract::TrustContractKind::Ensures,
            span: DUMMY_SP,
            predicate_digest: format!("sha256:{}", "z".repeat(64)),
            typed_proposition_digest: Some(zero_eq_typed_proposition_digest()),
            evidence: ClauseMonitorEvidence::Monitored(zero_eq_bound_monitor()),
        },
    ];
    stamp_certified_monitor_metadata_from_records(
        &records,
        &monitor_reference_function(&reference),
        &reference,
        &mut bundle,
    );

    let assert_metadata = |index: usize,
                           metadata: &[trust_verifier_api::MetadataEntry],
                           expected_status: &str,
                           expected_digest: &str| {
        let one = |key: &str| {
            let values = metadata
                .iter()
                .filter(|entry| entry.key == key)
                .map(|entry| entry.value.as_str())
                .collect::<Vec<_>>();
            assert_eq!(values.len(), 1, "index {index} must have exactly one `{key}`");
            values[0]
        };
        assert_eq!(one(TRUST_MONITOR_STATUS_METADATA_KEY), expected_status);
        assert_eq!(one(TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY), expected_digest);
        let reason = one(TRUST_MONITOR_REASON_METADATA_KEY);
        assert!(!reason.is_empty());
        assert!(
            reason.len() <= TRUST_MONITOR_REASON_MAX_BYTES,
            "index {index} reason exceeded the byte bound"
        );
        assert!(reason.is_char_boundary(reason.len()));
        if index == 1 {
            assert!(reason.ends_with('…'), "multibyte truncation must retain a valid ellipsis");
        }
    };

    for contract in &bundle.contracts {
        let index =
            monitor_contract_source_index(&contract.contract_id).expect("dense contract id");
        let (status, digest) = match index {
            0 => ("monitored", format!("sha256:{}", "a".repeat(64))),
            1 => ("unmonitored", format!("sha256:{}", "b".repeat(64))),
            2 => ("unmonitored", format!("sha256:{}", "c".repeat(64))),
            _ => unreachable!(),
        };
        assert_metadata(index, &contract.metadata, status, &digest);
    }

    for obligation in &bundle.obligations {
        let index = obligation
            .contract_id
            .as_deref()
            .and_then(monitor_contract_source_index)
            .or_else(|| obligation.obligation_id.rsplit(':').next()?.parse().ok())
            .expect("dense derived-obligation id");
        let (status, digest) = if obligation.description.contains("mismatched") {
            ("unmonitored", format!("sha256:{}", "d".repeat(64)))
        } else {
            match index {
                0 => ("monitored", format!("sha256:{}", "a".repeat(64))),
                1 => ("unmonitored", format!("sha256:{}", "b".repeat(64))),
                2 => ("unmonitored", format!("sha256:{}", "c".repeat(64))),
                3 => ("unmonitored", format!("sha256:{}", "e".repeat(64))),
                _ => unreachable!(),
            }
        };
        assert_metadata(index, &obligation.metadata, status, &digest);
    }

    assert_eq!(contract_ids.len(), 3, "fixture must retain all reordered contracts");
}

fn supported_static_monitor_fixture() -> (
    trust_verifier_api::TrustContractBundle,
    trust_verifier_api::TrustContractBundle,
    Vec<ClauseMonitorRecord>,
) {
    let function = trust_verifier_api::FunctionContext {
        crate_name: "monitor".to_string(),
        path: "monitor::supported".to_string(),
    };
    let contract_id = trust_types::canonical_contract_source_id(&function.path, "requires", 0);
    let source = trust_verifier_api::SourceLocation {
        file: Some("monitor.rs".to_string()),
        line: Some(11),
        column: Some(5),
        end_line: Some(11),
        end_column: Some(20),
    };
    let bound = zero_eq_bound_monitor();
    let typed_digest = trust_types::typed_contract_proposition_digest(
        &bound.static_formula,
        &bound.variable_domains,
    );
    let predicate_digest = "a".repeat(64);
    let source_digest = "d".repeat(64);
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "supported-static-monitor",
        trust_verifier_api::BundleSubject::Function {
            crate_name: function.crate_name.clone(),
            path: function.path.clone(),
        },
    );
    bundle.contracts.push(trust_verifier_api::TrustContract {
        contract_id: contract_id.clone(),
        kind: trust_verifier_api::ContractKind::Requires,
        predicate: trust_verifier_api::ContractPredicate::TrustExpr { text: "x == 0".to_string() },
        source: source.clone(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: "trust.contract.kind".to_string(),
                value: "requires".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: "trust.contract.lowering".to_string(),
                value: "typed_formula_v1".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: source_digest.clone(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest.clone(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: typed_digest.clone(),
            },
        ],
    });
    let context = trust_verifier_api::ObligationContext::new(
        trust_verifier_api::ObligationProducer::CompilerMirExtract,
        trust_verifier_api::ObligationOrigin::Contract {
            contract_id: contract_id.clone(),
            contract_kind: trust_verifier_api::ContractKind::Requires,
            contract_index: 0,
            predicate_schema: None,
        },
    )
    .with_function(function);
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: "obligation:monitor__supported:precondition:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Precondition,
        contract_id: Some(contract_id),
        proof_item_id: None,
        source,
        description: "prove requires contract".to_string(),
        required_strength: Some(trust_verifier_api::ProofStrength::deductive()),
        summary_facts: Vec::new(),
        metadata: vec![
            context.to_metadata_entry().expect("supported origin serializes"),
            trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: source_digest,
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest,
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: typed_digest.clone(),
            },
        ],
    });
    let reference = bundle.clone();
    let record = ClauseMonitorRecord {
        source_index: 0,
        kind: rustc_middle::mir::trust_contract::TrustContractKind::Requires,
        span: DUMMY_SP,
        predicate_digest: format!("sha256:{}", "b".repeat(64)),
        typed_proposition_digest: Some(typed_digest),
        evidence: ClauseMonitorEvidence::Monitored(bound),
    };
    (bundle, reference, vec![record])
}

fn monitor_reference_function(
    reference: &trust_verifier_api::TrustContractBundle,
) -> CompilerFunctionAuthority {
    CompilerFunctionAuthority::compatibility_for_test(monitor_reference_context(reference))
}

fn monitor_reference_context(
    reference: &trust_verifier_api::TrustContractBundle,
) -> trust_verifier_api::FunctionContext {
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &reference.subject
    else {
        panic!("monitor reference must have a function subject")
    };
    trust_verifier_api::FunctionContext { crate_name: crate_name.clone(), path: path.clone() }
}

fn bind_test_compiler_identity(
    bundle: &mut trust_verifier_api::TrustContractBundle,
    stable_crate_id: u64,
) {
    let trust_verifier_api::BundleSubject::Function { path, .. } = &bundle.subject else {
        panic!("compiler identity test bundle must have a function subject")
    };
    bundle.bundle_id = format!(
        "trust-contracts:{}:rustc-crate:{stable_crate_id:016x}",
        trust_types::canonical_artifact_id_component(path),
    );
    bundle.metadata.retain(|entry| entry.key != TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY);
    bundle.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY.to_string(),
        value: format!("{stable_crate_id:016x}"),
    });
}

#[test]
fn supported_static_monitor_requires_exact_reference_context_and_unique_row() {
    let (mut exact, reference, records) = supported_static_monitor_fixture();
    stamp_certified_monitor_metadata_from_records(
        &records,
        &monitor_reference_function(&reference),
        &reference,
        &mut exact,
    );
    assert_eq!(
        exactly_one_metadata_value(
            &exact.obligations[0].metadata,
            TRUST_MONITOR_STATUS_METADATA_KEY,
        ),
        Some("monitored"),
    );

    for mismatch in [
        "obligation-id",
        "missing-context",
        "duplicate-context",
        "producer",
        "origin-index",
        "origin-kind",
        "origin-variant",
        "context-crate",
        "context-path",
        "source",
        "description",
        "strength",
        "proof-item",
        "summary",
        "predicate-digest",
        "typed-digest",
        "contract-predicate",
        "subject-crate",
        "subject-path",
    ] {
        let (mut bundle, reference, records) = supported_static_monitor_fixture();
        match mismatch {
            "obligation-id" => bundle.obligations[0].obligation_id.push_str(":forged"),
            "missing-context" => bundle.obligations[0]
                .metadata
                .retain(|entry| entry.key != trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY),
            "duplicate-context" => {
                let context = bundle.obligations[0]
                    .metadata
                    .iter()
                    .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
                    .expect("fixture context")
                    .clone();
                bundle.obligations[0].metadata.push(context);
            }
            "producer" | "origin-index" | "origin-kind" | "origin-variant" | "context-crate"
            | "context-path" => {
                mutate_test_obligation_context(
                    &mut bundle.obligations[0],
                    |context| match mismatch {
                        "producer" => {
                            context.producer =
                                trust_verifier_api::ObligationProducer::Compatibility;
                        }
                        "origin-index" => {
                            let trust_verifier_api::ObligationOrigin::Contract {
                                contract_index,
                                ..
                            } = &mut context.origin
                            else {
                                unreachable!()
                            };
                            *contract_index = 1;
                        }
                        "origin-kind" => {
                            let trust_verifier_api::ObligationOrigin::Contract {
                                contract_kind,
                                ..
                            } = &mut context.origin
                            else {
                                unreachable!()
                            };
                            *contract_kind = trust_verifier_api::ContractKind::Ensures;
                        }
                        "origin-variant" => {
                            context.origin =
                                trust_verifier_api::ObligationOrigin::VerificationCondition {
                                    vc_kind: "precondition".to_string(),
                                    vc_index: 0,
                                    formula_schema: None,
                                };
                        }
                        "context-crate" => {
                            context.function.as_mut().expect("function").crate_name =
                                "attacker".to_string();
                        }
                        "context-path" => {
                            context.function.as_mut().expect("function").path =
                                "monitor::other".to_string();
                        }
                        _ => unreachable!(),
                    },
                );
            }
            "source" => bundle.obligations[0].source.line = Some(99),
            "description" => bundle.obligations[0].description = "forged".to_string(),
            "strength" => bundle.obligations[0].required_strength = None,
            "proof-item" => {
                bundle.obligations[0].proof_item_id = Some("forged".to_string());
            }
            "summary" => {
                bundle.obligations[0].summary_facts.push(fresh_rekey_tampered_summary_fact())
            }
            "predicate-digest" => {
                bundle.obligations[0]
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
                    .expect("predicate digest")
                    .value = "c".repeat(64)
            }
            "typed-digest" => {
                bundle.obligations[0]
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
                    .expect("typed digest")
                    .value = format!("sha256:{}", "c".repeat(64))
            }
            "contract-predicate" => {
                bundle.contracts[0].predicate =
                    trust_verifier_api::ContractPredicate::TrustExpr { text: "true".to_string() };
            }
            "subject-crate" => {
                let trust_verifier_api::BundleSubject::Function { crate_name, .. } =
                    &mut bundle.subject
                else {
                    unreachable!()
                };
                *crate_name = "attacker".to_string();
            }
            "subject-path" => {
                let trust_verifier_api::BundleSubject::Function { path, .. } = &mut bundle.subject
                else {
                    unreachable!()
                };
                *path = "monitor::other".to_string();
            }
            _ => unreachable!(),
        }
        stamp_certified_monitor_metadata_from_records(
            &records,
            &monitor_reference_function(&reference),
            &reference,
            &mut bundle,
        );
        assert_eq!(
            exactly_one_metadata_value(
                &bundle.obligations[0].metadata,
                TRUST_MONITOR_STATUS_METADATA_KEY,
            ),
            Some("unmonitored"),
            "mismatch `{mismatch}` must fail closed",
        );
    }

    let (mut jointly_substituted, mut substituted_reference, records) =
        supported_static_monitor_fixture();
    let compiler_expected = monitor_reference_function(&substituted_reference);
    for bundle in [&mut jointly_substituted, &mut substituted_reference] {
        let trust_verifier_api::BundleSubject::Function { path, .. } = &mut bundle.subject else {
            unreachable!()
        };
        *path = "attacker::substituted".to_string();
        mutate_test_obligation_context(&mut bundle.obligations[0], |context| {
            context.function.as_mut().expect("function context").path =
                "attacker::substituted".to_string();
        });
    }
    stamp_certified_monitor_metadata_from_records(
        &records,
        &compiler_expected,
        &substituted_reference,
        &mut jointly_substituted,
    );
    assert_eq!(
        exactly_one_metadata_value(
            &jointly_substituted.obligations[0].metadata,
            TRUST_MONITOR_STATUS_METADATA_KEY,
        ),
        Some("unmonitored"),
        "a jointly substituted reference, bundle, and context must not authenticate itself",
    );

    let (mut duplicated, reference, records) = supported_static_monitor_fixture();
    duplicated.obligations.push(duplicated.obligations[0].clone());
    stamp_certified_monitor_metadata_from_records(
        &records,
        &monitor_reference_function(&reference),
        &reference,
        &mut duplicated,
    );
    assert!(duplicated.obligations.iter().all(|obligation| {
        exactly_one_metadata_value(&obligation.metadata, TRUST_MONITOR_STATUS_METADATA_KEY)
            == Some("unmonitored")
    }));

    let (mut mixed, reference, records) = supported_static_monitor_fixture();
    let mut forged = mixed.obligations[0].clone();
    forged.obligation_id.push_str(":forged");
    mixed.obligations.push(forged);
    stamp_certified_monitor_metadata_from_records(
        &records,
        &monitor_reference_function(&reference),
        &reference,
        &mut mixed,
    );
    assert_eq!(
        exactly_one_metadata_value(
            &mixed.obligations[0].metadata,
            TRUST_MONITOR_STATUS_METADATA_KEY,
        ),
        Some("monitored"),
    );
    assert_eq!(
        exactly_one_metadata_value(
            &mixed.obligations[1].metadata,
            TRUST_MONITOR_STATUS_METADATA_KEY,
        ),
        Some("unmonitored"),
    );
}

#[test]
fn certified_monitor_requires_exact_compiler_crate_instance_identity() {
    const EXPECTED_STABLE_ID: u64 = 0xaa;
    let (mut exact, mut reference, records) = supported_static_monitor_fixture();
    bind_test_compiler_identity(&mut exact, EXPECTED_STABLE_ID);
    bind_test_compiler_identity(&mut reference, EXPECTED_STABLE_ID);
    let authority =
        CompilerFunctionAuthority::exact(monitor_reference_context(&reference), EXPECTED_STABLE_ID);
    stamp_certified_monitor_metadata_from_records(&records, &authority, &reference, &mut exact);
    assert_eq!(
        exactly_one_metadata_value(
            &exact.obligations[0].metadata,
            TRUST_MONITOR_STATUS_METADATA_KEY,
        ),
        Some("monitored"),
    );

    for mismatch in [
        "missing-sidecar",
        "duplicate-sidecar",
        "uppercase-sidecar",
        "wrong-sidecar",
        "wrong-bundle-id",
        "joint-other-crate-instance",
    ] {
        let (mut bundle, mut reference, records) = supported_static_monitor_fixture();
        bind_test_compiler_identity(&mut bundle, EXPECTED_STABLE_ID);
        bind_test_compiler_identity(&mut reference, EXPECTED_STABLE_ID);
        let authority = CompilerFunctionAuthority::exact(
            monitor_reference_context(&reference),
            EXPECTED_STABLE_ID,
        );
        match mismatch {
            "missing-sidecar" => bundle
                .metadata
                .retain(|entry| entry.key != TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY),
            "duplicate-sidecar" => bundle.metadata.push(trust_verifier_api::MetadataEntry {
                key: TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY.to_string(),
                value: format!("{EXPECTED_STABLE_ID:016x}"),
            }),
            "uppercase-sidecar" => {
                bundle
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY)
                    .expect("stable crate identity")
                    .value = "00000000000000AA".to_string();
            }
            "wrong-sidecar" => {
                bundle
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY)
                    .expect("stable crate identity")
                    .value = "0000000000000022".to_string();
            }
            "wrong-bundle-id" => bundle.bundle_id.push_str(":forged"),
            "joint-other-crate-instance" => {
                bind_test_compiler_identity(&mut bundle, 0x22);
                bind_test_compiler_identity(&mut reference, 0x22);
            }
            _ => unreachable!(),
        }
        stamp_certified_monitor_metadata_from_records(
            &records,
            &authority,
            &reference,
            &mut bundle,
        );
        assert_eq!(
            exactly_one_metadata_value(
                &bundle.obligations[0].metadata,
                TRUST_MONITOR_STATUS_METADATA_KEY,
            ),
            Some("unmonitored"),
            "mismatch `{mismatch}` must fail closed",
        );
    }
}

fn unsupported_static_monitor_fixture() -> (
    trust_verifier_api::TrustContractBundle,
    trust_verifier_api::TrustContractBundle,
    Vec<ClauseMonitorRecord>,
) {
    let function_path = "monitor::f";
    let contract_id = "trust-contract:monitor::f:requires:0".to_string();
    let reason = "unsupported_machine_arithmetic: the static verifier cannot represent exact u8 wrapping arithmetic".to_string();
    let predicate_digest = "a".repeat(64);
    let bound_monitor = u8_wrapping_bound_monitor();
    let typed_proposition_digest = trust_types::typed_contract_proposition_digest(
        &bound_monitor.static_formula,
        &bound_monitor.variable_domains,
    );
    let source = trust_verifier_api::SourceLocation {
        file: Some("monitor.rs".to_string()),
        line: Some(7),
        column: Some(3),
        end_line: Some(7),
        end_column: Some(20),
    };
    let mut bundle = trust_verifier_api::TrustContractBundle::empty(
        "unsupported-static-monitor",
        trust_verifier_api::BundleSubject::Function {
            crate_name: "monitor".to_string(),
            path: function_path.to_string(),
        },
    );
    bundle.contracts.push(trust_verifier_api::TrustContract {
        contract_id: contract_id.clone(),
        kind: trust_verifier_api::ContractKind::Requires,
        predicate: trust_verifier_api::ContractPredicate::Unsupported { reason: reason.clone() },
        source: source.clone(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: "trust.contract.kind".to_string(),
                value: "requires".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: "trust.contract.unsupported_reason".to_string(),
                value: reason.clone(),
            },
            trust_verifier_api::MetadataEntry {
                key: "trust.contract.lowering".to_string(),
                value: "unsupported".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: "d".repeat(64),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest.clone(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: typed_proposition_digest.clone(),
            },
        ],
    });
    let context = trust_verifier_api::ObligationContext::new(
        trust_verifier_api::ObligationProducer::CompilerMirExtract,
        trust_verifier_api::ObligationOrigin::UnsupportedContract {
            contract_index: 0,
            compiler_contract_kind: "requires".to_string(),
            reason: reason.clone(),
        },
    )
    .with_function(trust_verifier_api::FunctionContext {
        crate_name: "monitor".to_string(),
        path: function_path.to_string(),
    });
    bundle.obligations.push(trust_verifier_api::TrustObligation {
        obligation_id: "unsupported:monitor__f:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.contract".to_string(),
            name: "unsupported".to_string(),
        },
        contract_id: Some(contract_id),
        proof_item_id: None,
        source,
        description: reason,
        required_strength: Some(trust_verifier_api::ProofStrength::deductive()),
        summary_facts: Vec::new(),
        metadata: vec![
            context.to_metadata_entry().expect("unsupported origin serializes"),
            trust_verifier_api::MetadataEntry {
                key: "trust.contract.kind".to_string(),
                value: "requires".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest,
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: typed_proposition_digest.clone(),
            },
        ],
    });

    let record = ClauseMonitorRecord {
        source_index: 0,
        kind: rustc_middle::mir::trust_contract::TrustContractKind::Requires,
        span: DUMMY_SP,
        predicate_digest: format!("sha256:{}", "b".repeat(64)),
        typed_proposition_digest: Some(typed_proposition_digest),
        evidence: ClauseMonitorEvidence::Monitored(bound_monitor),
    };
    let reference = bundle.clone();
    (bundle, reference, vec![record])
}

fn replace_unsupported_static_monitor_context(
    obligation: &mut trust_verifier_api::TrustObligation,
    context: trust_verifier_api::ObligationContext,
) {
    obligation
        .metadata
        .retain(|entry| entry.key != trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY);
    obligation.metadata.push(context.to_metadata_entry().expect("replacement origin serializes"));
}

#[test]
fn unsupported_static_marker_inherits_exact_private_certified_monitor() {
    let (mut bundle, reference, records) = unsupported_static_monitor_fixture();
    let ClauseMonitorEvidence::Monitored(bound) = &records[0].evidence else {
        panic!("fixture must carry compiler-private certified monitor evidence")
    };
    assert!(
        bound.runtime.evaluate(&[("x", u8::MAX.into()), ("y", 1)]).unwrap(),
        "the certified runtime lane must retain u8 wrapping semantics"
    );
    stamp_certified_monitor_metadata_from_records(
        &records,
        &monitor_reference_function(&reference),
        &reference,
        &mut bundle,
    );

    let trust_verifier_api::ContractPredicate::Unsupported { reason } =
        &bundle.contracts[0].predicate
    else {
        panic!("runtime monitor evidence must not erase the static unsupported row")
    };
    assert!(reason.contains("unsupported_machine_arithmetic"));

    for metadata in [&bundle.contracts[0].metadata, &bundle.obligations[0].metadata] {
        assert_eq!(
            exactly_one_metadata_value(metadata, TRUST_MONITOR_STATUS_METADATA_KEY),
            Some("monitored")
        );
        assert_eq!(
            exactly_one_metadata_value(metadata, TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY),
            Some(format!("sha256:{}", "b".repeat(64)).as_str())
        );
    }
}

#[test]
fn unsupported_static_marker_rejects_every_identity_mismatch() {
    for mismatch in [
        "origin-index",
        "origin-kind",
        "origin-producer",
        "origin-schema",
        "obligation-digest",
        "duplicate-digest",
        "obligation-typed-digest",
        "missing-obligation-typed-digest",
        "duplicate-obligation-typed-digest",
        "supported-contract-predicate",
        "contract-reason",
        "obligation-id",
        "noncanonical-contract-id",
        "duplicate-contract",
        "source-location",
    ] {
        let (mut bundle, reference, records) = unsupported_static_monitor_fixture();
        match mismatch {
            "origin-index" | "origin-kind" | "origin-producer" | "origin-schema" => {
                let mut context =
                    exactly_one_obligation_context(&bundle.obligations[0]).expect("fixture origin");
                match mismatch {
                    "origin-index" => {
                        let trust_verifier_api::ObligationOrigin::UnsupportedContract {
                            contract_index,
                            ..
                        } = &mut context.origin
                        else {
                            unreachable!()
                        };
                        *contract_index = 1;
                    }
                    "origin-kind" => {
                        let trust_verifier_api::ObligationOrigin::UnsupportedContract {
                            compiler_contract_kind,
                            ..
                        } = &mut context.origin
                        else {
                            unreachable!()
                        };
                        *compiler_contract_kind = "ensures".to_string();
                    }
                    "origin-producer" => {
                        context.producer = trust_verifier_api::ObligationProducer::Compatibility;
                    }
                    "origin-schema" => context.schema_version = "forged-schema".to_string(),
                    _ => unreachable!(),
                }
                replace_unsupported_static_monitor_context(&mut bundle.obligations[0], context);
            }
            "obligation-digest" => {
                bundle.obligations[0]
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
                    .expect("fixture digest")
                    .value = "c".repeat(64);
            }
            "duplicate-digest" => {
                bundle.obligations[0].metadata.push(trust_verifier_api::MetadataEntry {
                    key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                    value: "a".repeat(64),
                });
            }
            "obligation-typed-digest" => {
                bundle.obligations[0]
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
                    .expect("fixture typed proposition digest")
                    .value = format!("sha256:{}", "c".repeat(64));
            }
            "missing-obligation-typed-digest" => {
                bundle.obligations[0].metadata.retain(|entry| {
                    entry.key != TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY
                });
            }
            "duplicate-obligation-typed-digest" => {
                bundle.obligations[0].metadata.push(trust_verifier_api::MetadataEntry {
                    key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                    value: zero_eq_typed_proposition_digest(),
                });
            }
            "supported-contract-predicate" => {
                bundle.contracts[0].predicate =
                    trust_verifier_api::ContractPredicate::TrustExpr { text: "true".to_string() };
            }
            "contract-reason" => {
                bundle.contracts[0]
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == "trust.contract.unsupported_reason")
                    .expect("fixture unsupported reason")
                    .value = "different reason".to_string();
            }
            "obligation-id" => {
                bundle.obligations[0].obligation_id = "unsupported:attacker:0".to_string();
            }
            "noncanonical-contract-id" => {
                let malformed = "trust-contract:monitor::f:requires:00".to_string();
                bundle.contracts[0].contract_id = malformed.clone();
                bundle.obligations[0].contract_id = Some(malformed);
            }
            "duplicate-contract" => bundle.contracts.push(bundle.contracts[0].clone()),
            "source-location" => bundle.obligations[0].source.line = Some(8),
            _ => unreachable!(),
        }

        stamp_certified_monitor_metadata_from_records(
            &records,
            &monitor_reference_function(&reference),
            &reference,
            &mut bundle,
        );
        assert_eq!(
            exactly_one_metadata_value(
                &bundle.obligations[0].metadata,
                TRUST_MONITOR_STATUS_METADATA_KEY,
            ),
            Some("unmonitored"),
            "mismatch `{mismatch}` must fail closed"
        );
    }
}

#[test]
fn certified_monitor_contract_identity_uses_shared_canonical_path_encoding() {
    let record = ClauseMonitorRecord {
        source_index: 7,
        kind: rustc_middle::mir::trust_contract::TrustContractKind::Requires,
        span: DUMMY_SP,
        predicate_digest: format!("sha256:{}", "a".repeat(64)),
        typed_proposition_digest: None,
        evidence: ClauseMonitorEvidence::Unmonitored { reason: "fixture".to_string() },
    };
    let impl_path = "<sealed_dyn_probe::Button as sealed_dyn_probe::sealed::Widget>::rank";
    let canonical = trust_types::canonical_contract_source_id(impl_path, "requires", 7);
    assert!(canonical.contains("%20as%20"));
    assert!(canonical_monitor_contract_id_matches_record(&record, &canonical, impl_path));
    assert!(!canonical_monitor_contract_id_matches_record(
        &record,
        "trust-contract:<sealed_dyn_probe::Button as sealed_dyn_probe::sealed::Widget>::rank:requires:7",
        impl_path,
    ));

    let escaped_looking_path =
        "<sealed_dyn_probe::Button%20as%20sealed_dyn_probe::sealed::Widget>::rank";
    assert_ne!(
        canonical,
        trust_types::canonical_contract_source_id(escaped_looking_path, "requires", 7)
    );
    assert!(!canonical_monitor_contract_id_matches_record(
        &record,
        &canonical,
        escaped_looking_path,
    ));

    let long_path = format!("sealed_dyn_probe::{}", "nested::".repeat(300));
    let long_id = trust_types::canonical_contract_source_id(&long_path, "requires", 7);
    assert!(long_id.contains("%~sha256~"));
    assert!(canonical_monitor_contract_id_matches_record(&record, &long_id, &long_path));
    assert!(!canonical_monitor_contract_id_matches_record(
        &record,
        &format!("trust-contract:{long_path}:requires:7"),
        &long_path,
    ));
}

#[test]
fn public_monitor_metadata_cannot_mint_certified_status() {
    let (mut bundle, reference, _) = unsupported_static_monitor_fixture();
    for metadata in [&mut bundle.contracts[0].metadata, &mut bundle.obligations[0].metadata] {
        metadata.extend([
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_STATUS_METADATA_KEY.to_string(),
                value: "monitored".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_REASON_METADATA_KEY.to_string(),
                value: "forged verifier metadata".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "f".repeat(64)),
            },
        ]);
    }

    stamp_certified_monitor_metadata_from_records(
        &[],
        &monitor_reference_function(&reference),
        &reference,
        &mut bundle,
    );
    for metadata in [&bundle.contracts[0].metadata, &bundle.obligations[0].metadata] {
        assert_eq!(
            exactly_one_metadata_value(metadata, TRUST_MONITOR_STATUS_METADATA_KEY),
            Some("unmonitored"),
            "only compiler-private records may create Monitored"
        );
    }
}

// ---------------------------------------------------------------------------
// Trust (wave-3): the BV legacy-row decoder. `formula_from_trust_spec_expr` /
// `reconstruct_obligation_violation_formula` must decode the payload schema's
// bitvector fragment FAITHFULLY (the decoded formula is what the kernel
// re-certifies and what the vacuity precheck inspects before ANY proof
// authority mints) and fail closed on every node they cannot reverse exactly.
// ---------------------------------------------------------------------------

/// A minimal obligation whose only proof-relevant content is the typed
/// `trust.vc.formula.payload` metadata entry built from `predicate`.
fn obligation_with_formula_payload(
    predicate: &trust_verifier_api::TrustSpecPredicate,
) -> trust_verifier_api::TrustObligation {
    trust_verifier_api::TrustObligation {
        obligation_id: "vc:demo:arithmetic_safety:0".to_string(),
        kind: trust_verifier_api::ObligationKind::Custom {
            namespace: "trust.vc.test".to_string(),
            name: "arithmetic_safety".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: trust_verifier_api::SourceLocation::default(),
        description: "decoder round-trip".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(predicate).expect("TrustSpecPredicate serializes"),
            },
        ],
    }
}

#[test]
fn bv_payload_reconstructs_the_real_violation_formula() {
    use trust_verifier_api::{
        TrustSpecBinaryOp as Bin, TrustSpecBvBinaryOp as BvBin, TrustSpecBvUnaryOp as BvUn,
        TrustSpecExpr, TrustSpecSort, TrustSpecVariable, TrustSpecVariableOrigin,
    };

    // The float-overflow witness residue shape (`a + b: f64`): sign bits agree
    // AND the left operand's exponent is finite — pure QF_BV over BitVec(64)
    // parameter leaves, exactly what vcgen emits and PDR proves.
    let bv64 = TrustSpecSort::BitVec { width: 64 };
    let lhs = TrustSpecExpr::variable("_1", bv64);
    let rhs = TrustSpecExpr::variable("_2", bv64);
    let sign_bit = |operand: &TrustSpecExpr| {
        TrustSpecExpr::bv_unary(BvUn::Extract { high: 63, low: 63 }, operand.clone(), 1)
    };
    let root = TrustSpecExpr::binary(
        Bin::And,
        TrustSpecExpr::binary(Bin::Eq, sign_bit(&lhs), sign_bit(&rhs)),
        TrustSpecExpr::bv_binary(
            BvBin::Ult,
            TrustSpecExpr::bv_unary(BvUn::Extract { high: 62, low: 52 }, lhs.clone(), 11),
            TrustSpecExpr::bitvec_literal("2047", 11),
            11,
        ),
    );
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        root,
        vec![
            TrustSpecVariable {
                name: "_1".to_string(),
                sort: bv64,
                origin: TrustSpecVariableOrigin::Local { index: 1 },
            },
            TrustSpecVariable {
                name: "_2".to_string(),
                sort: bv64,
                origin: TrustSpecVariableOrigin::Local { index: 2 },
            },
        ],
    );

    let formula =
        reconstruct_obligation_violation_formula(&obligation_with_formula_payload(&predicate))
            .expect("a BV-payload row must keep its REAL violation formula, not the placeholder");

    let bx = Box::new;
    let var64 = |name: &str| bx(Formula::Var(name.to_string(), trust_types::Sort::BitVec(64)));
    let expected = Formula::And(vec![
        Formula::Eq(
            bx(Formula::BvExtract { inner: var64("_1"), high: 63, low: 63 }),
            bx(Formula::BvExtract { inner: var64("_2"), high: 63, low: 63 }),
        ),
        Formula::BvULt(
            bx(Formula::BvExtract { inner: var64("_1"), high: 62, low: 52 }),
            bx(Formula::BitVec { value: 2047, width: 11 }),
            11,
        ),
    ]);
    assert_eq!(formula, expected);
    // The exact veto this decoder removes: a reconstructed BV row is opaque to
    // the boolean-skeleton evaluator, so the vacuity precheck inside
    // `build_result_proof_authorities` passes instead of vetoing the proof.
    assert!(!trust_router::constant_folder::violation_formula_is_vacuously_unsat(&formula));
}

#[test]
fn bv_payload_conversions_and_arithmetic_decode_faithfully() {
    use trust_verifier_api::{
        TrustSpecBinaryOp as Bin, TrustSpecBvBinaryOp as BvBin, TrustSpecBvUnaryOp as BvUn,
        TrustSpecExpr, TrustSpecSort,
    };

    // (bv2nat(bvadd(int2bv(n, 8), #x01)) == 0) ∧ bvslt(sign_extend(bvnot(x)), 0)
    // — exercises BvFromInt, IntFromBv (unsigned flag threaded), BV arithmetic,
    // BvNot, SignExt, a signed comparison, and BitVec literals in one predicate.
    let bv8 = TrustSpecSort::BitVec { width: 8 };
    let sum = TrustSpecExpr::bv_binary(
        BvBin::Add,
        TrustSpecExpr::bv_from_int(TrustSpecExpr::variable("n", TrustSpecSort::Int), 8),
        TrustSpecExpr::bitvec_literal("1", 8),
        8,
    );
    let widened_not = TrustSpecExpr::bv_unary(
        BvUn::SignExt { extend_by: 8 },
        TrustSpecExpr::bv_unary(BvUn::Not, TrustSpecExpr::variable("x", bv8), 8),
        16,
    );
    let root = TrustSpecExpr::binary(
        Bin::And,
        TrustSpecExpr::binary(
            Bin::Eq,
            TrustSpecExpr::int_from_bv(sum, false, 8),
            TrustSpecExpr::int_literal("0"),
        ),
        TrustSpecExpr::bv_binary(
            BvBin::Slt,
            widened_not,
            TrustSpecExpr::bitvec_literal("0", 16),
            16,
        ),
    );

    let formula = formula_from_trust_spec_expr(&root).expect("the composite BV shape decodes");

    let bx = Box::new;
    let expected = Formula::And(vec![
        Formula::Eq(
            bx(Formula::BvToInt(
                bx(Formula::BvAdd(
                    bx(Formula::IntToBv(
                        bx(Formula::Var("n".to_string(), trust_types::Sort::Int)),
                        8,
                    )),
                    bx(Formula::BitVec { value: 1, width: 8 }),
                    8,
                )),
                8,
                false,
            )),
            bx(Formula::Int(0)),
        ),
        Formula::BvSLt(
            bx(Formula::BvSignExt(
                bx(Formula::BvNot(
                    bx(Formula::Var("x".to_string(), trust_types::Sort::BitVec(8))),
                    8,
                )),
                8,
            )),
            bx(Formula::BitVec { value: 0, width: 16 }),
            16,
        ),
    ]);
    assert_eq!(formula, expected);
}

#[test]
fn undecodable_node_inside_bv_payload_keeps_the_fail_closed_placeholder() {
    use trust_verifier_api::{TrustSpecBvBinaryOp as BvBin, TrustSpecExpr, TrustSpecSort};

    // `old(x)` has no `Formula` inverse. The WHOLE row must fail closed (`None`
    // → the caller keeps `Bool(false)`), never a guessed sub-formula.
    let bv64 = TrustSpecSort::BitVec { width: 64 };
    let root = TrustSpecExpr::bv_binary(
        BvBin::Ult,
        TrustSpecExpr::old(TrustSpecExpr::variable("x", bv64)),
        TrustSpecExpr::bitvec_literal("5", 64),
        64,
    );
    let predicate = trust_verifier_api::TrustSpecPredicate::new(root, Vec::new());
    assert_eq!(
        reconstruct_obligation_violation_formula(&obligation_with_formula_payload(&predicate)),
        None,
    );
}

#[test]
fn ugt_uge_payload_nodes_fail_closed() {
    use trust_verifier_api::{TrustSpecBvBinaryOp as BvBin, TrustSpecExpr, TrustSpecSort};

    // No `Formula` produces `Ugt`/`Uge`, so a payload containing one cannot be
    // the encoder's image — the decoder must refuse it rather than guess an
    // operand-swapped equivalent.
    let bv64 = TrustSpecSort::BitVec { width: 64 };
    for op in [BvBin::Ugt, BvBin::Uge] {
        let root = TrustSpecExpr::bv_binary(
            op,
            TrustSpecExpr::variable("x", bv64),
            TrustSpecExpr::variable("y", bv64),
            64,
        );
        assert_eq!(formula_from_trust_spec_expr(&root), None, "{op:?} must fail closed");
    }
}

#[test]
fn malformed_bv_payload_sort_disagreement_fails_closed() {
    use trust_verifier_api::{
        TrustSpecBvBinaryOp as BvBin, TrustSpecBvUnaryOp as BvUn, TrustSpecExpr, TrustSpecExprKind,
        TrustSpecSort,
    };

    let bv = |width: u32| TrustSpecSort::BitVec { width };
    let var64 = TrustSpecExpr::variable("x", bv(64));

    // (a) literal whose node sort disagrees with its stamped width.
    let lying_literal = TrustSpecExpr {
        sort: bv(8),
        kind: TrustSpecExprKind::BitVecLiteral { value: "1".to_string(), width: 16 },
    };
    assert_eq!(formula_from_trust_spec_expr(&lying_literal), None);

    // (b) extract whose stamped width disagrees with the slice `[3:0]`.
    let lying_extract = TrustSpecExpr {
        sort: bv(5),
        kind: TrustSpecExprKind::BvUnary {
            op: BvUn::Extract { high: 3, low: 0 },
            expr: Box::new(var64.clone()),
            width: 5,
        },
    };
    assert_eq!(formula_from_trust_spec_expr(&lying_extract), None);

    // (c) sign-extension by zero (the encoder refuses to produce it).
    let zero_extend = TrustSpecExpr {
        sort: bv(64),
        kind: TrustSpecExprKind::BvUnary {
            op: BvUn::SignExt { extend_by: 0 },
            expr: Box::new(var64.clone()),
            width: 64,
        },
    };
    assert_eq!(formula_from_trust_spec_expr(&zero_extend), None);

    // (d) binary comparison whose operand widths disagree with the op width.
    let mismatched_compare = TrustSpecExpr {
        sort: TrustSpecSort::Bool,
        kind: TrustSpecExprKind::BvBinary {
            op: BvBin::Ult,
            lhs: Box::new(TrustSpecExpr::variable("narrow", bv(32))),
            rhs: Box::new(var64),
            width: 64,
        },
    };
    assert_eq!(formula_from_trust_spec_expr(&mismatched_compare), None);

    // (e) non-decimal literal text (never encoder-produced).
    assert_eq!(formula_from_trust_spec_expr(&TrustSpecExpr::bitvec_literal("0x1f", 8)), None);
}

#[test]
fn non_bool_root_bv_payload_fails_closed() {
    use trust_verifier_api::TrustSpecExpr;

    // A decodable BV node, but a BitVec-sorted ROOT is not a proposition — the
    // compiler encoder only ever mints Bool roots, so this is a foreign payload.
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        TrustSpecExpr::bitvec_literal("7", 64),
        Vec::new(),
    );
    assert_eq!(
        reconstruct_obligation_violation_formula(&obligation_with_formula_payload(&predicate)),
        None,
    );
}

#[test]
fn bool_literal_payload_still_maps_to_the_placeholder() {
    use trust_verifier_api::TrustSpecExpr;

    // must-NOT twin: widening the decoder must not start treating the literal
    // `Bool(false)` bookkeeping placeholder as a reconstructable real formula.
    let predicate =
        trust_verifier_api::TrustSpecPredicate::new(TrustSpecExpr::bool_literal(false), Vec::new());
    assert_eq!(
        reconstruct_obligation_violation_formula(&obligation_with_formula_payload(&predicate)),
        None,
    );
}

// ---------------------------------------------------------------------------
// Trust (wave-3): the derived-total certificate fallback row must be explicit
// evidence that stays fail-closed in every consumer.
// ---------------------------------------------------------------------------

#[test]
fn derived_total_certificate_row_is_explicit_and_fail_closed() {
    let row = transport_derived_total_certificate_row();
    assert_eq!(row.kind, "derived-total-certificate");
    assert_eq!(row.outcome, Outcome::Unknown);
    assert_eq!(row.solver, "trust-compiler");
    // Every fail-closed consumer must stay engaged: the row blocks extern-call
    // demotion, folds into the native-lowering assumption collapse (it is not a
    // proof or refutation that must survive), and is not mistaken for the
    // absent-callee panic class.
    assert!(transport_row_blocks_extern_call_demotion(&row));
    assert!(!native_lowering_collapse_keeps_row(&row));
    assert!(!transport_row_is_unproved_assumption_panic(&row));
}

#[test]
fn derived_total_fallback_summary_shape_stays_fatal_under_strict() {
    // must-NOT twin: the certificate fallback keeps `summary.total == 0` and
    // `full_verification: None`, and that zero-inventory shape must REMAIN a
    // strict-lane failure (skipped: 1) — the explicit certificate row is
    // evidence, never proof credit, so a derived body that genuinely cannot
    // lower must not become silently green.
    let summary = TrustFunctionSummary {
        total: 0,
        trusted: 0,
        certified: 0,
        cached: 0,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        max_level: TrustProofLevel::None,
    };
    // Mirror `derived_total_artifacts` exactly: the certificate is the whole
    // transport inventory, while no native result, binding, or proof-authority
    // row exists that could authenticate it as proof credit.
    let transport_results = [transport_derived_total_certificate_row()];
    let results: [(VerificationCondition, VerificationResult); 0] = [];
    let result_bindings: [Option<ResultObligationBinding>; 0] = [];
    let proof_authorities: [Option<ResultProofAuthority>; 0] = [];
    let failure = full_verification_failure(
        &summary,
        &transport_results,
        &results,
        &result_bindings,
        &proof_authorities,
    )
    .expect("the zero-inventory certificate fallback must stay a strict failure");
    assert_eq!(
        failure,
        FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 1 },
    );
    assert!(strict_failure_is_fatal(failure));
}

// ---------------------------------------------------------------------------
// Trust #540 / composition review 2026-07-18 — R1 flip-seam hardening + C2
// mint guards. Finding (c): the narrowed-ambiguity refusal (proved co-matches
// must not shrink the MF-1 population to a single wrong row); finding (a):
// the designed R1-establisher exclusion in the ensures-marker mint; finding
// (b): the authored-clause cross-check.
// ---------------------------------------------------------------------------

fn r1_test_var(name: &str) -> trust_types::Formula {
    trust_types::Formula::Var(name.to_string(), trust_types::Sort::Int)
}

/// `P = (name != 0)` — the shape the R1 harvest's `¬V`/proposer lane gates to
/// parameter-only variables.
fn r1_test_nonzero_assumption(name: &str) -> trust_types::Formula {
    trust_types::Formula::Not(Box::new(trust_types::Formula::Eq(
        Box::new(r1_test_var(name)),
        Box::new(trust_types::Formula::Int(0)),
    )))
}

#[test]
fn r1_flip_decision_refuses_multiple_unproved_matches_regardless_of_binding() {
    // MF-1 is independent of the narrowed-binding predicate: >= 2 unproved
    // key-sharers refuse even if the certificate would "bind" one of them.
    assert_eq!(r1_flip_decision(2, &[4, 7], |_| true), R1FlipDecision::RefuseAmbiguous);
    assert_eq!(r1_flip_decision(3, &[0, 1, 2], |_| true), R1FlipDecision::RefuseAmbiguous);
}

#[test]
fn r1_flip_decision_narrowed_two_row_key_refuses_when_unbound() {
    // THE finding-(c) regression shape: a two-row key where one row is already
    // proved (full-lane bridge / `promote_kernel_certifiable` run BEFORE the
    // flip seam). The old unproved-only match set saw a single row and flipped
    // it — the proved row HID the ambiguity MF-1 would have refused. The
    // narrowed case now requires the certificate to bind the sole unproved
    // row; unbound refuses.
    assert_eq!(r1_flip_decision(2, &[5], |_| false), R1FlipDecision::RefuseNarrowed);
    assert_eq!(r1_flip_decision(4, &[9], |_| false), R1FlipDecision::RefuseNarrowed);
}

#[test]
fn r1_flip_decision_narrowed_two_row_key_applies_when_bound() {
    // The `flip_caller_covered`/`flip_private_reachable` per-key layout: a
    // proved co-match (the division's other vcgen encoding, natively proved)
    // plus the single unproved isolated row, with the certificate's assumption
    // connected to that row — the sole-unproved-match rule admits the flip.
    assert_eq!(
        r1_flip_decision(2, &[5], |index| {
            assert_eq!(index, 5, "binding must be evaluated on the sole unproved row");
            true
        }),
        R1FlipDecision::Apply(5)
    );
}

#[test]
fn r1_flip_decision_unique_match_does_not_consult_binding() {
    // A unique key match that is the sole unproved row is unambiguous by
    // construction — the pre-review behavior, preserved bit-for-bit (the
    // binding predicate must not even run: pre-opt/post-opt formula drift on
    // the general single-match population must not regress admitted flips).
    assert_eq!(
        r1_flip_decision(1, &[3], |_| unreachable!(
            "unique key match must not consult the narrowed-binding predicate"
        )),
        R1FlipDecision::Apply(3)
    );
}

#[test]
fn r1_flip_decision_without_unproved_matches_is_no_target() {
    // No key match at all, and the all-matches-already-proved population: in
    // both cases there is nothing to discharge (a flip onto a proved row would
    // be a no-op and the sealed token stays unconsumed).
    assert_eq!(r1_flip_decision(0, &[], |_| true), R1FlipDecision::NoTarget);
    assert_eq!(r1_flip_decision(3, &[], |_| true), R1FlipDecision::NoTarget);
}

#[test]
fn r1_narrowed_binding_connects_assumption_to_row_operand() {
    // P = divisor != 0 over the parameter base name; the row's per-body vcgen
    // formula carries SSA-versioned spellings (`divisor#s0_1`). The
    // version-stripped base-name comparison binds them.
    let p = r1_test_nonzero_assumption("divisor");
    let row = trust_types::Formula::And(vec![
        trust_types::Formula::Eq(
            Box::new(r1_test_var("_3#s0_1")),
            Box::new(trust_types::Formula::Bool(true)),
        ),
        trust_types::Formula::Eq(
            Box::new(r1_test_var("divisor#s0_1")),
            Box::new(trust_types::Formula::Int(0)),
        ),
    ]);
    assert!(r1_narrowed_flip_assumption_binds_row(&p, Some(&row)));
}

#[test]
fn r1_narrowed_binding_refuses_macro_twin_over_different_operand() {
    // The finding-(c) hazard scenario: the certificate was harvested for the
    // same-key operation over `b`; the sole unproved row is a DIFFERENT
    // operation over `d` (macro-twin spans sharing kind+file+line+col). P is
    // not connected to the row's violation, so the certificate cannot be the
    // one that discharges it — refuse.
    let p = r1_test_nonzero_assumption("b");
    let row = trust_types::Formula::Eq(
        Box::new(r1_test_var("d#s0_2")),
        Box::new(trust_types::Formula::Int(0)),
    );
    assert!(!r1_narrowed_flip_assumption_binds_row(&p, Some(&row)));
}

#[test]
fn r1_narrowed_binding_fails_closed_without_source_formula() {
    // Full-lane rows answer only through the recovered per-body vcgen formula
    // (`R1NativeRowFlipKey::source_formula`); recovery failure must refuse the
    // narrowed flip, never fall back to the transport placeholder.
    let p = r1_test_nonzero_assumption("b");
    assert!(!r1_narrowed_flip_assumption_binds_row(&p, None));
}

#[test]
fn r1_narrowed_binding_refuses_closed_assumption() {
    // A closed P constrains nothing row-distinguishing. Unreachable past the
    // mint's connectedness check, but the seam must not rely on that.
    assert!(!r1_narrowed_flip_assumption_binds_row(
        &trust_types::Formula::Bool(true),
        Some(&r1_test_var("divisor"))
    ));
}

#[test]
fn r1_variable_base_name_strips_version_tokens_only() {
    assert_eq!(r1_variable_base_name("divisor#s0_1"), "divisor");
    assert_eq!(r1_variable_base_name("divisor"), "divisor");
    assert_eq!(r1_variable_base_name("_4#s0_3_s1_0"), "_4");
}

#[test]
fn r1_recursive_callsite_inventory_is_exact_and_multiplicity_preserving() {
    let span = |line| trust_types::SourceSpan {
        file: "src/lib.rs".to_string(),
        line_start: line,
        col_start: 4,
        line_end: line,
        col_end: 12,
    };
    let first = span(10);
    let second = span(20);

    assert!(exact_callsite_span_multiset_matches(
        &[first.clone(), first.clone(), second.clone()],
        &[second.clone(), first.clone(), first.clone()],
    ));
    assert!(
        !exact_callsite_span_multiset_matches(
            &[first.clone(), first.clone()],
            std::slice::from_ref(&first),
        ),
        "one produced row must not discharge two same-span recursive calls",
    );
    assert!(
        !exact_callsite_span_multiset_matches(
            std::slice::from_ref(&first),
            &[first.clone(), second],
        ),
        "an extra producer row must not enter the sealed recursive proof",
    );
}

/// Budget and worker-limit arithmetic decides when the pass stops asking
/// solvers questions. A saturating or silently-defaulting bound would turn a
/// configured budget into the built-in one and change which obligations get
/// answered at all, so the clamping edges are pinned here.
mod runtime_config_tests {
    use super::*;

    use super::*;

    #[test]
    fn zero_function_budget_disables_deadline() {
        assert!(verify_fn_deadline_from_ms(0, std::time::Instant::now()).is_none());
    }

    #[test]
    fn huge_function_budget_clamps_without_becoming_the_default() {
        let now = std::time::Instant::now();
        let deadline = verify_fn_deadline_from_ms(u64::MAX, now)
            .expect("a positive configured budget must produce a deadline");
        let default_ms =
            rustc_session::config::Options::default().unstable_opts.trust_verify_function_budget_ms;

        assert!(
            deadline > now + std::time::Duration::from_millis(default_ms),
            "an overflowing huge budget must not silently shrink to the 120-second default"
        );
    }

    #[test]
    fn solver_timeout_is_capped_by_remaining_function_budget() {
        let now = std::time::Instant::now();
        let deadline = now + std::time::Duration::from_millis(37);
        assert_eq!(remaining_solver_timeout_ms(500, Some(deadline), now), Some(37));
        assert_eq!(remaining_solver_timeout_ms(11, Some(deadline), now), Some(11));
        assert_eq!(remaining_solver_timeout_ms(500, None, now), Some(500));
    }

    #[test]
    fn expired_function_budget_starts_no_new_solver_query() {
        let now = std::time::Instant::now();
        let expired = now.checked_sub(std::time::Duration::from_millis(1)).unwrap();
        assert_eq!(remaining_solver_timeout_ms(500, Some(expired), now), None);
    }

    #[test]
    fn sub_millisecond_remaining_budget_still_gets_one_millisecond() {
        let now = std::time::Instant::now();
        let deadline = now + std::time::Duration::from_nanos(1);
        assert_eq!(remaining_solver_timeout_ms(500, Some(deadline), now), Some(1));
    }

    #[test]
    fn full_verifier_worker_limit_is_capped_to_resource_limit_width() {
        assert_eq!(verify_worker_thread_limit_from(4), Some(4));
        assert_eq!(verify_worker_thread_limit_from(256), Some(256));
        assert_eq!(verify_worker_thread_limit_from(usize::from(u16::MAX) + 1), None);
        assert_eq!(verify_worker_thread_limit_from(0), None);
        assert_eq!(verify_worker_thread_limit_from(1), Some(1));
    }

    #[test]
    fn full_verifier_context_carries_deadline_and_worker_limit() {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(1);
        let context = full_verifier_execution_context_from("run-limited", Some(deadline), Some(2));

        assert_eq!(context.deadline(), Some(deadline));
        assert_eq!(context.limits.worker_threads, Some(2));
    }

    #[test]
    fn full_verifier_context_applies_positive_worker_cap() {
        let worker_threads = verify_worker_thread_limit_from(3);
        let context = full_verifier_execution_context_from("run-worker-cap", None, worker_threads);

        assert_eq!(context.limits.worker_threads, Some(3));
    }

    #[test]
    fn full_verifier_context_ignores_zero_worker_cap() {
        for configured in [0] {
            let worker_threads = verify_worker_thread_limit_from(configured);
            let context =
                full_verifier_execution_context_from("run-default-workers", None, worker_threads);

            assert!(context.limits.worker_threads.is_none());
            assert!(!context.limits.has_any_limit());
        }
    }

    #[test]
    fn full_verifier_context_stays_unlimited_without_worker_limit() {
        let context = full_verifier_execution_context_from("run-unlimited", None, None);

        assert!(context.deadline().is_none());
        assert!(!context.limits.has_any_limit());
    }

    #[test]
    fn full_verifier_run_id_is_canonical_for_impl_def_paths() {
        let run_id = full_verifier_run_id("<demo::Button as demo::sealed::Widget>::rank");
        let context = full_verifier_execution_context_from(run_id, None, None);
        let bundle = trust_verifier_api::TrustContractBundle::empty(
            "bundle-run-id-test",
            trust_verifier_api::BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "<demo::Button as demo::sealed::Widget>::rank".to_string(),
            },
        );
        let result = trust_router::FullVerificationEngine::with_required_native_engines()
            .verify_bundle(&bundle, &context);

        result
            .validate_derived_state()
            .expect("compiler-generated impl run IDs must form canonical verifier envelopes");
    }
}
