// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Typed E9 evidence for actual checked Clean islands, not Rust-body refinement.

use trust_spec_elab::{Admission, Carrier, Domain, FacetTable, FnFacets};
use trust_types::{Formula, SourceSpan, VcKind};

use super::super::{
    admit_certified_island_definition, check_clean_island_into, island_definition_carriers,
};
use super::*;

const SOURCE: &str = r#"
inductive E9Choice : Type where
  | later : Nat -> E9Choice
  | earlier : Bool -> E9Choice

structure E9Record : Type where
  count : Nat
  flag : Bool

inductive E9Pair (A : Type) (B : Type) : Type where
  | mk : A -> B -> E9Pair A B

def e9_choice_id (x : E9Choice) : E9Choice := x
def e9_choice_copy (x : E9Choice) : E9Choice := x
def e9_choice_first (x : E9Choice) (y : E9Choice) : E9Choice := x
def e9_choice_constant (x : E9Choice) : E9Choice := E9Choice.earlier Bool.false
def e9_record_id (x : E9Record) : E9Record := x
def e9_pair_id (x : E9Pair Bool Nat) : E9Pair Bool Nat := x
def e9_pair_swapped (x : E9Pair Nat Bool) : E9Pair Nat Bool := x
def e9_from_nat (n : Nat) : E9Choice := E9Choice.later n
def e9_same_from_nat (n : Nat) : E9Choice := E9Choice.later n
def e9_nat_id (n : Nat) : Nat := n
def e9_u64_id (x : UInt64) : UInt64 := x
theorem e9_choice_refl (x : E9Choice) : x = x := rfl
"#;

fn fixture(source: &str) -> (Environment, FacetTable) {
    let mut env = Environment::with_prelude();
    let outcome = check_clean_island_into(source, &mut env);
    assert!(!outcome.is_rejected(), "real island registration: {:?}", outcome.errors);
    assert!(outcome.standin_imports.is_empty());
    let mut facets = FacetTable::new();
    for name in [
        "e9_choice_id",
        "e9_choice_copy",
        "e9_choice_first",
        "e9_choice_constant",
        "e9_record_id",
        "e9_pair_id",
        "e9_pair_swapped",
        "e9_from_nat",
        "e9_same_from_nat",
        "e9_nat_id",
        "e9_u64_id",
    ] {
        let admission = admit_certified_island_definition(&env, name, &mut facets)
            .expect("production island admitter");
        assert!(admission.require_kernel_check().is_ok());
    }
    (env, facets)
}

fn result_domain(env: &Environment, name: &str) -> Domain {
    let carriers = island_definition_carriers(env, name).expect("actual checked telescope");
    let Carrier::RegisteredAdt(adt) = carriers.ret else {
        panic!("fixture must expose a registered result carrier");
    };
    adt.validate_in(env).expect("current environment");
    Domain::RegisteredAdt(adt)
}

fn defeq<'a>(
    source: &'a str,
    referent: &'a str,
    facets: &'a FacetTable,
) -> EnsuresDischargeClause<'a> {
    EnsuresDischargeClause {
        clause_src: source,
        route: EnsuresDischargeRoute::IslandDefeq(referent),
        facets,
    }
}

fn row(function: &str) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: trust_types::Symbol::intern(function),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

fn roundtrip(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    params: &[(&str, Domain)],
    name: &str,
) -> EnsuresDischargeCertificate {
    let certificate = certify_ensures_discharge_with_domains(env, clauses, params, name)
        .expect("typed model judgment must mint");
    assert!(!certificate.term.is_empty());
    assert!(certificate.context.starts_with(b"trust-certify.e9-ensures-discharge.context.v2\0"));
    assert!(audit_presented_ensures_discharge(env, &certificate.term, &certificate.context));
    let vc = row(name);
    let evidence = certificate.evidence_for_row(&vc).expect("actual obligation binding");
    assert!(recheck_ensures_discharge_with_domains(env, clauses, params, name, &vc, &evidence));
    // KR0 switch: the typed lane also calls the reference entry, and the row's
    // payload carries exactly that certificate.
    let reference = certificate.reference().expect("the reference entry accepts the judgment");
    assert_eq!(reference.theory_id(), clean_kernel::TheoryId::LeanReferenceV1);
    assert_eq!(crate::reference_certificate_for(&evidence).as_ref(), Some(reference));
    certificate
}

#[test]
fn typed_enum_record_and_generic_identity_certificates_roundtrip() {
    let (env, facets) = fixture(SOURCE);
    for name in ["e9_choice_id", "e9_record_id", "e9_pair_id"] {
        let params = [("x", result_domain(&env, name))];
        let clauses = [defeq("result == x", name, &facets)];
        let first = roundtrip(&env, &clauses, &params, name);
        assert_eq!(first, roundtrip(&env, &clauses, &params, name), "canonical bytes");
    }
    let params = [("x", result_domain(&env, "e9_choice_id"))];
    let cited = EnsuresDischargeClause {
        clause_src: "result == x",
        route: EnsuresDischargeRoute::CitedTheorem("e9_choice_refl"),
        facets: &facets,
    };
    let _ = roundtrip(&env, &[cited], &params, "e9_choice_id");
    let _ = roundtrip(
        &env,
        &[cited, defeq("result == x", "e9_choice_id", &facets)],
        &params,
        "e9_choice_id",
    );
}

#[test]
fn typed_scalar_input_keeps_registered_result_only_dependencies() {
    let (env, _) = fixture(SOURCE);
    // No unrelated registered parameter admission may accidentally provide the
    // descriptor: both of these exact callees take Nat and return E9Choice.
    let result_facets = |env: &Environment| {
        let mut facets = FacetTable::new();
        for name in ["e9_from_nat", "e9_same_from_nat"] {
            let admission = admit_certified_island_definition(env, name, &mut facets).unwrap();
            let carriers = admission.carriers.as_ref().unwrap();
            assert_eq!(carriers.params, vec![Carrier::Nat]);
            assert!(matches!(carriers.ret, Carrier::RegisteredAdt(_)));
        }
        facets
    };
    let facets = result_facets(&env);
    let params = [("n", Domain::Nat)];
    let clauses = [defeq("result == e9_same_from_nat(n)", "e9_same_from_nat", &facets)];
    let certificate = roundtrip(&env, &clauses, &params, "e9_from_nat");
    let changed = SOURCE.replace(
        "  | later : Nat -> E9Choice\n  | earlier : Bool -> E9Choice",
        "  | earlier : Bool -> E9Choice\n  | later : Nat -> E9Choice",
    );
    assert_ne!(changed, SOURCE);
    let (twin, _) = fixture(&changed);
    let twin_facets = result_facets(&twin);
    let twin_clauses = [defeq("result == e9_same_from_nat(n)", "e9_same_from_nat", &twin_facets)];
    let _ = roundtrip(&twin, &twin_clauses, &params, "e9_from_nat");
    let goal = trust_spec_elab::elaborate_ensures_with_domains(
        &env,
        clauses[0].clause_src,
        &params,
        "e9_from_nat",
        &facets,
    )
    .unwrap();
    let proof = deserialize_term(&certificate.term).unwrap();
    assert!(
        twin.audit_certification(&goal, &proof).is_certified(),
        "constructor reorder preserves this judgment; v2 metadata must distinguish it"
    );
    assert!(!audit_presented_ensures_discharge(&twin, &certificate.term, &certificate.context));
    let vc = row("e9_from_nat");
    assert!(!recheck_ensures_discharge_with_domains(
        &twin,
        &twin_clauses,
        &params,
        "e9_from_nat",
        &vc,
        &certificate.evidence_for_row(&vc).unwrap()
    ));
}

#[test]
fn typed_parameter_identity_order_and_full_schema_are_bound() {
    let (env, facets) = fixture(SOURCE);
    let name = "e9_pair_id";
    let params = [("x", result_domain(&env, name))];
    let clauses = [defeq("result == x", name, &facets)];
    let certificate = roundtrip(&env, &clauses, &params, name);
    let vc = row(name);
    let evidence = certificate.evidence_for_row(&vc).unwrap();
    for wrong in [
        vec![("x", result_domain(&env, "e9_pair_swapped"))],
        vec![("x", Domain::Nat)],
        vec![("renamed", params[0].1.clone())],
        vec![("x", params[0].1.clone()), ("x", params[0].1.clone())],
        vec![],
    ] {
        assert!(!recheck_ensures_discharge_with_domains(
            &env, &clauses, &wrong, name, &vc, &evidence
        ));
    }
    let choice = result_domain(&env, "e9_choice_first");
    let ordered = [("x", choice.clone()), ("y", choice.clone())];
    let reversed = [("y", choice.clone()), ("x", choice)];
    let same = [defeq("result == result", "e9_choice_first", &facets)];
    let first = roundtrip(&env, &same, &ordered, "e9_choice_first");
    let first_vc = row("e9_choice_first");
    assert!(
        !recheck_ensures_discharge_with_domains(
            &env,
            &same,
            &reversed,
            "e9_choice_first",
            &first_vc,
            &first.evidence_for_row(&first_vc).unwrap()
        ),
        "same-domain parameter order must be bound even for a reflexive conclusion"
    );

    let changed = SOURCE.replace("  count : Nat", "  count : Bool");
    assert_ne!(changed, SOURCE);
    let (twin, twin_facets) = fixture(&changed);
    let old = [("x", result_domain(&env, "e9_record_id"))];
    let fresh = [("x", result_domain(&twin, "e9_record_id"))];
    assert_ne!(old, fresh);
    let old_clauses = [defeq("result == x", "e9_record_id", &facets)];
    let old_certificate = roundtrip(&env, &old_clauses, &old, "e9_record_id");
    let fresh_clauses = [defeq("result == x", "e9_record_id", &twin_facets)];
    let _ = roundtrip(&twin, &fresh_clauses, &fresh, "e9_record_id");
    assert!(
        certify_ensures_discharge_with_domains(&twin, &fresh_clauses, &old, "e9_record_id")
            .is_none()
    );
    assert!(!audit_presented_ensures_discharge(
        &twin,
        &old_certificate.term,
        &old_certificate.context
    ));
}

#[test]
fn typed_consumer_binds_clause_order_referent_function_and_obligation() {
    let (env, facets) = fixture(SOURCE);
    let name = "e9_choice_id";
    let params = [("x", result_domain(&env, name))];
    let clauses = [
        defeq("result == x", name, &facets),
        defeq("result == e9_choice_copy(x)", "e9_choice_copy", &facets),
    ];
    let certificate = roundtrip(&env, &clauses, &params, name);
    let vc = row(name);
    let evidence = certificate.evidence_for_row(&vc).unwrap();
    for changed in [
        vec![clauses[1], clauses[0]],
        vec![clauses[0]],
        vec![defeq("result == e9_choice_id(x)", name, &facets), clauses[1]],
        vec![defeq("result == x", "e9_choice_copy", &facets), clauses[1]],
    ] {
        let _ = roundtrip(&env, &changed, &params, name);
        assert!(
            !recheck_ensures_discharge_with_domains(&env, &changed, &params, name, &vc, &evidence),
            "different but provable authored inputs must not consume the original certificate"
        );
    }
    let mut changed_row = vc.clone();
    changed_row.formula = Formula::Bool(false);
    for other in [row("another_function"), changed_row] {
        assert!(!recheck_ensures_discharge_with_domains(
            &env, &clauses, &params, name, &other, &evidence
        ));
    }
    assert!(!recheck_ensures_discharge_with_domains(
        &env,
        &clauses,
        &params,
        "e9_choice_copy",
        &vc,
        &evidence
    ));
}

#[test]
fn typed_payload_rejects_tampering_trailing_bytes_and_cross_version_splicing() {
    let (env, facets) = fixture(SOURCE);
    let name = "e9_choice_id";
    let params = [("x", result_domain(&env, name))];
    let clauses = [defeq("result == x", name, &facets)];
    let good = roundtrip(&env, &clauses, &params, name);
    let mut bad_term = good.clone();
    *bad_term.term.last_mut().unwrap() ^= 1;
    let mut trailing_term = good.clone();
    trailing_term.term.push(0);
    let mut bad_context = good.clone();
    *bad_context.context.last_mut().unwrap() ^= 1;
    let mut trailing_context = good.clone();
    trailing_context.context.push(0);
    let mut wrong_version = good.clone();
    let v2 = b"trust-certify.e9-ensures-discharge.context.v2\0";
    wrong_version.context[..v2.len()]
        .copy_from_slice(b"trust-certify.e9-ensures-discharge.context.v1\0");
    let vc = row(name);
    for forged in [bad_term, trailing_term, bad_context, trailing_context, wrong_version] {
        assert_ne!(good, forged);
        assert!(!audit_presented_ensures_discharge(&env, &forged.term, &forged.context));
        // Recompute the row hash: these are not merely stale-lineage controls.
        let evidence = forged.evidence_for_row(&vc).unwrap();
        assert!(!recheck_ensures_discharge_with_domains(
            &env, &clauses, &params, name, &vc, &evidence
        ));
    }
}

#[test]
fn typed_false_actual_self_result_and_partial_surface_mint_nothing() {
    let (env, facets) = fixture(SOURCE);
    let params = [("x", result_domain(&env, "e9_choice_id"))];
    let positive = defeq("result == x", "e9_choice_id", &facets);
    let _ = roundtrip(&env, &[positive], &params, "e9_choice_id");
    let wrong = defeq("result == x", "e9_choice_constant", &facets);
    let goal = trust_spec_elab::elaborate_ensures_with_domains(
        &env,
        wrong.clause_src,
        &params,
        "e9_choice_constant",
        &facets,
    )
    .expect("false contract is still well typed");
    let candidate = super::super::defeq_closed_proof(&goal).unwrap();
    assert!(clean_kernel::TypeChecker::new(&env).infer_type(&candidate).is_ok());
    assert!(clean_kernel::TypeChecker::new(&env).check_type(&candidate, &goal).is_err());
    assert!(
        certify_ensures_discharge_with_domains(&env, &[wrong], &params, "e9_choice_constant")
            .is_none()
    );
    let true_sibling = defeq("result == result", "e9_choice_constant", &facets);
    let _ = roundtrip(&env, &[true_sibling], &params, "e9_choice_constant");
    for surface in [vec![true_sibling, wrong], vec![wrong, true_sibling], vec![]] {
        assert!(
            certify_ensures_discharge_with_domains(&env, &surface, &params, "e9_choice_constant")
                .is_none()
        );
    }
}

#[test]
fn typed_model_evidence_does_not_upgrade_reflected_admission() {
    let (env, certified) = fixture(SOURCE);
    let name = "e9_choice_id";
    let original = certified.admitted(name).unwrap();
    let reflected = Admission::reflected(name, original.arity)
        .with_declared_signature(original.return_domain().cloned(), original.carriers.clone());
    assert!(reflected.require_kernel_check().is_err());
    let mut facets = FacetTable::new();
    facets.insert(
        name,
        FnFacets::from_structural_certificates(true, true, true, true, "test reflection"),
    );
    facets.admit(name, reflected.clone());
    let params = [("x", result_domain(&env, name))];
    let clauses = [defeq("result == x", name, &facets)];
    let _ = roundtrip(&env, &clauses, &params, name);
    assert_eq!(facets.admitted(name), Some(&reflected));
    assert!(
        facets.admitted(name).unwrap().require_kernel_check().is_err(),
        "a certificate of the checked Clean equation does not certify the reflected Rust body"
    );
}

#[test]
fn typed_strict_lane_preserves_scalar_v1_and_does_not_enable_proof_lifts() {
    let (env, facets) = fixture(SOURCE);
    let name = "e9_nat_id";
    let clauses = [defeq("result == n", name, &facets)];
    let strings = [("n", "nat")];
    let domains = [("n", Domain::Nat)];
    let strict = trust_spec_elab::ProofClauseInputs::strict();
    let legacy = certify_ensures_discharge(&env, &clauses, &strings, name, &strict).unwrap();
    let typed = roundtrip(&env, &clauses, &domains, name);
    assert!(legacy.context.starts_with(b"trust-certify.e9-ensures-discharge.context.v1\0"));
    assert_eq!(legacy.term, typed.term);
    assert_ne!(legacy.context, typed.context);
    assert!(audit_presented_ensures_discharge(&env, &legacy.term, &legacy.context));
    let vc = row(name);
    let old_evidence = legacy.evidence_for_row(&vc).unwrap();
    let typed_evidence = typed.evidence_for_row(&vc).unwrap();
    assert!(recheck_ensures_discharge(&env, &clauses, &strings, name, &strict, &vc, &old_evidence));
    assert!(!recheck_ensures_discharge_with_domains(
        &env,
        &clauses,
        &domains,
        name,
        &vc,
        &old_evidence
    ));
    assert!(!recheck_ensures_discharge(
        &env,
        &clauses,
        &strings,
        name,
        &strict,
        &vc,
        &typed_evidence
    ));
    let lifted = [defeq("result as nat == e9_nat_id(x as nat)", "e9_nat_id", &facets)];
    let scalar_strings = [("x", "u64")];
    let scalar_domains = [("x", Domain::Machine(trust_spec_elab::MachineUIntWidth::U64))];
    let lift = trust_spec_elab::ProofClauseInputs::proof_lift(Some("u64"));
    assert!(
        certify_ensures_discharge(&env, &lifted, &scalar_strings, "e9_u64_id", &lift).is_some()
    );
    assert!(
        certify_ensures_discharge_with_domains(&env, &lifted, &scalar_domains, "e9_u64_id")
            .is_none()
    );
}

#[test]
fn typed_session_mints_before_failure_but_refuses_after_taint() {
    let mut session = super::super::CleanIslandSession::new();
    let outcome = session.check(SOURCE);
    assert!(!outcome.is_rejected(), "session island: {:?}", outcome.errors);
    assert!(!session.is_tainted());
    let mut facets = FacetTable::new();
    let env = session.environment().unwrap();
    let _ = admit_certified_island_definition(env, "e9_pair_id", &mut facets).unwrap();
    let params = [("x", result_domain(env, "e9_pair_id"))];
    let clauses = [defeq("result == x", "e9_pair_id", &facets)];
    let certificate = session
        .certify_ensures_discharge_with_domains(&clauses, &params, "e9_pair_id")
        .expect("untainted session");
    assert_eq!(certificate, roundtrip(env, &clauses, &params, "e9_pair_id"));
    // An actual rejected island, not a fabricated taint field, closes the API.
    assert!(session.check("def e9_rejected : Nat := Bool.false\n").is_rejected());
    assert!(session.is_tainted());
    assert!(session.environment().is_none());
    assert!(
        session.certify_ensures_discharge_with_domains(&clauses, &params, "e9_pair_id").is_none()
    );
}

#[test]
fn typed_environment_digest_binds_datatypes_reached_only_by_the_proof() {
    use clean_kernel::{BinderInfo, Declaration, Level};

    // The unused let is retained in the actual kernel-checked theorem value.
    // No registered parameter or facet handle can supply this dependency.
    let proof = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::let_named(
            Name::from_string("witness"),
            Expr::const_str("E9Choice"),
            Expr::app(Expr::const_str("E9Choice.later"), Expr::bvar(0)),
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                [Expr::const_str("Nat"), Expr::bvar(1)],
            ),
            false,
        ),
    );
    let statement = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Nat"), Expr::bvar(0), Expr::bvar(0)],
        ),
    );
    let scalar_fixture = |source: &str| {
        let (mut env, _) = fixture(source);
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("e9_nat_via_choice"),
            level_params: vec![],
            type_: statement.clone(),
            value: proof.clone(),
        })
        .unwrap();
        assert_eq!(
            env.get_const(&Name::from_string("e9_nat_via_choice")).unwrap().value.as_ref(),
            Some(&proof)
        );
        let mut facets = FacetTable::new();
        let _ = admit_certified_island_definition(&env, "e9_nat_id", &mut facets).unwrap();
        assert!(facets.registered_carriers().is_empty());
        (env, facets)
    };
    let (env, facets) = scalar_fixture(SOURCE);
    let clauses = [EnsuresDischargeClause {
        clause_src: "result == n",
        route: EnsuresDischargeRoute::CitedTheorem("e9_nat_via_choice"),
        facets: &facets,
    }];
    let params = [("n", Domain::Nat)];
    let certificate = roundtrip(&env, &clauses, &params, "e9_nat_id");
    assert_eq!(deserialize_term(&certificate.term).unwrap(), proof);
    let audit = env.audit_certification(&statement, &proof);
    assert!(audit.is_certified());
    assert!(
        audit.dependencies.contains(&Name::from_string("E9Choice")),
        "proof dependency must really be reached"
    );
    let reordered = SOURCE.replace(
        "  | later : Nat -> E9Choice\n  | earlier : Bool -> E9Choice",
        "  | earlier : Bool -> E9Choice\n  | later : Nat -> E9Choice",
    );
    let changed_field = SOURCE
        .replace("earlier : Bool", "earlier : Nat")
        .replace("E9Choice.earlier Bool.false", "E9Choice.earlier 0");
    for (changed, same_root_metadata) in [(reordered, false), (changed_field, true)] {
        assert_ne!(changed, SOURCE);
        let (twin, twin_facets) = scalar_fixture(&changed);
        if same_root_metadata {
            // The unchanged root record and unchanged proof are insufficient:
            // only closure traversal reaches the unused constructor's new type.
            let key = Name::from_string("E9Choice");
            assert_eq!(
                trust_spec_elab::canonical_declaration_binding(&env, &key).unwrap(),
                trust_spec_elab::canonical_declaration_binding(&twin, &key).unwrap()
            );
        }
        let twin_clauses = [EnsuresDischargeClause { facets: &twin_facets, ..clauses[0] }];
        assert!(twin.audit_certification(&statement, &proof).is_certified());
        let _ = roundtrip(&twin, &twin_clauses, &params, "e9_nat_id");
        assert!(
            !audit_presented_ensures_discharge(&twin, &certificate.term, &certificate.context),
            "a valid scalar proof cannot erase changed reachable constructor metadata"
        );
        let vc = row("e9_nat_id");
        assert!(!recheck_ensures_discharge_with_domains(
            &twin,
            &twin_clauses,
            &params,
            "e9_nat_id",
            &vc,
            &certificate.evidence_for_row(&vc).unwrap()
        ));
    }
}
