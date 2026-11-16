use super::super::*;

fn vc_of_kind(kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: trust_types::Symbol::intern("test::f"),
        location: trust_types::SourceSpan::default(),
        formula: trust_types::Formula::Bool(false),
        contract_metadata: None,
        // Not a vertical-slice emitter: no authenticated-obligation record.
        obligation: None,
    }
}

fn proved() -> VerificationResult {
    VerificationResult::Proved {
        solver: trust_types::Symbol::intern("test-proof"),
        time_ms: 0,
        strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn unknown() -> VerificationResult {
    VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("test-unknown"),
        time_ms: 0,
        reason: "unproved".to_string(),
    }
}

/// An UNCONDITIONAL static-proof authority sealed to row `index`/`vc`.
fn unconditional_authority(index: usize, vc: &VerificationCondition) -> ResultProofAuthority {
    ResultProofAuthority::InterproceduralCalleeClosure {
        row: exact_result_row_identity(index, vc)
            .expect("constructed VC must serialize to a row identity"),
    }
}

// Part A soundness lock. Panic-freedom registration is decoupled from
// FUNCTIONAL correctness: a proved panic site + an UNKNOWN functional
// postcondition still registers, but ANY unproved PANIC-SITE row (or the
// panic-freedom catch-all) must block registration, and a function carrying
// only unproved postconditions must fail closed.

#[test]
fn proved_panic_site_with_unknown_postcondition_registers() {
    // `#[trust::ensures(|_r| true)]` shape: the only unproved row is the
    // functional postcondition; the panic site is a proved unconditional
    // static proof. Panic-freedom is established, so it registers.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let post = vc_of_kind(VcKind::Postcondition);
    let auth = unconditional_authority(0, &div);
    let results = vec![(div, proved()), (post, unknown())];
    let authorities = vec![Some(auth), None];
    assert!(
        results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "a proved panic site with an unproved functional postcondition must register pf"
    );
}

#[test]
fn unproved_panic_site_does_not_register() {
    // Adversarial: a genuinely-panicking function (its division-by-zero panic
    // site is UNKNOWN) must NEVER register panic-free, even though its
    // postcondition is (irrelevantly) exempt.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let post = vc_of_kind(VcKind::Postcondition);
    let results = vec![(div, unknown()), (post, unknown())];
    let authorities = vec![None, None];
    assert!(
        !results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "an unproved panic site must block panic-freedom registration"
    );
}

#[test]
fn unproved_panic_freedom_catchall_does_not_register() {
    // Adversarial: the whole-function panic-freedom catch-all is an
    // `Assertion`, NOT a `Postcondition`, so an UNKNOWN catch-all must block
    // registration even beside a proved panic site.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let catchall = vc_of_kind(VcKind::Assertion {
        message: "panic freedom: no assertion, `unreachable!`, or panic is reachable".to_string(),
    });
    let auth = unconditional_authority(0, &div);
    let results = vec![(div, proved()), (catchall, unknown())];
    let authorities = vec![Some(auth), None];
    assert!(
        !results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "an unproved panic-freedom catch-all must block registration"
    );
}

#[test]
fn only_unproved_postconditions_fails_closed() {
    // Fail-closed: zero positive panic evidence (the only row is an unproved
    // postcondition) must NOT register.
    let post = vc_of_kind(VcKind::Postcondition);
    let results = vec![(post, unknown())];
    let authorities = vec![None];
    assert!(
        !results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "a function whose only row is an unproved postcondition must fail closed"
    );
}

#[test]
fn proved_postcondition_beside_proved_panic_site_still_registers() {
    // A genuinely-proved (non-vacuous) postcondition is likewise fine: the
    // exemption widens what may stay Unknown; it never blocks a proved row.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let post = vc_of_kind(VcKind::Postcondition);
    let auth0 = unconditional_authority(0, &div);
    let auth1 = unconditional_authority(1, &post);
    let results = vec![(div, proved()), (post, proved())];
    let authorities = vec![Some(auth0), Some(auth1)];
    assert!(
        results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "all-proved rows (incl. a proved postcondition) must still register"
    );
}

// ---- Postcondition-only leaf (the 2026-09-12 strict-lane regression) ----

#[test]
fn all_proved_postconditions_is_the_postcondition_only_shape() {
    // `clamp_upper(v, hi) ensures result <= hi { if v > hi { hi } else { v } }`:
    // every row is a proved, unconditionally-authorized Postcondition and
    // there is no panic site. The relaxed predicate's positive-evidence
    // guard refuses it (no non-postcondition row exists to be proved), and
    // that refusal is what the pure helper must recognise as its shape.
    let p0 = vc_of_kind(VcKind::Postcondition);
    let p1 = vc_of_kind(VcKind::Postcondition);
    let auth0 = unconditional_authority(0, &p0);
    let auth1 = unconditional_authority(1, &p1);
    let results = vec![(p0, proved()), (p1, proved())];
    let authorities = vec![Some(auth0), Some(auth1)];
    assert!(
        !results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "the relaxed predicate keeps refusing the shape (its guard is about the ROW KIND)"
    );
    assert!(
        results_are_only_proved_unconditional_postconditions(&results, &[], &authorities),
        "every row a proved unconditional postcondition must be recognised as the shape"
    );
}

#[test]
fn postcondition_only_shape_refuses_an_unproved_postcondition() {
    // The exemption is not widened: an UNPROVED postcondition beside a proved
    // one is still "zero positive panic evidence" and fails closed on BOTH
    // predicates.
    let p0 = vc_of_kind(VcKind::Postcondition);
    let p1 = vc_of_kind(VcKind::Postcondition);
    let auth0 = unconditional_authority(0, &p0);
    let results = vec![(p0, proved()), (p1, unknown())];
    let authorities = vec![Some(auth0), None];
    assert!(!results_establish_unconditional_panic_freedom(&results, &[], &authorities));
    assert!(
        !results_are_only_proved_unconditional_postconditions(&results, &[], &authorities),
        "an unproved postcondition must not read as the all-proved shape"
    );
}

#[test]
fn postcondition_only_shape_refuses_a_proved_row_without_authority() {
    // `Proved` with an EMPTY authority slot is not an unconditional static
    // proof (a demoted None-authority row); the shape must fail closed.
    let p0 = vc_of_kind(VcKind::Postcondition);
    let results = vec![(p0, proved())];
    let authorities = vec![None];
    assert!(!results_are_only_proved_unconditional_postconditions(&results, &[], &authorities));
}

#[test]
fn postcondition_only_shape_refuses_a_panic_site_row() {
    // A proved panic-site row makes this the ORDINARY lane's business, not
    // the postcondition-only lane's: the helper is exact about the kind.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let post = vc_of_kind(VcKind::Postcondition);
    let auth0 = unconditional_authority(0, &div);
    let auth1 = unconditional_authority(1, &post);
    let results = vec![(div, proved()), (post, proved())];
    let authorities = vec![Some(auth0), Some(auth1)];
    assert!(results_establish_unconditional_panic_freedom(&results, &[], &authorities));
    assert!(!results_are_only_proved_unconditional_postconditions(&results, &[], &authorities));
}

#[test]
fn postcondition_only_shape_refuses_an_empty_set() {
    // The empty set is the zero-obligation twin's case, never this one.
    assert!(!results_are_only_proved_unconditional_postconditions(&[], &[], &[]));
}

// ---- Part B: under-precondition registration soundness locks ----

fn proved_with_solver(tag: &str) -> VerificationResult {
    VerificationResult::Proved {
        solver: trust_types::Symbol::intern(tag),
        time_ms: 0,
        strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn pf_catchall() -> VerificationCondition {
    vc_of_kind(VcKind::Assertion {
        message: "panic freedom: no assertion, `unreachable!`, or panic is reachable".to_string(),
    })
}

fn contract(kind: trust_types::ContractKind) -> trust_types::Contract {
    trust_types::Contract {
        kind,
        span: trust_types::SourceSpan::default(),
        body: "lo <= hi".to_string(),
    }
}

fn test_func() -> trust_types::VerifiableFunction {
    trust_types::VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: trust_types::SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: Vec::new(),
            blocks: Vec::new(),
            arg_count: 0,
            return_ty: trust_types::Ty::Bool,
            // The empty body names no datatypes (R0 out-of-band defs).
            datatype_defs: trust_types::DatatypeDefs::new(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The EXACT authenticated pf catch-all obligation for `func` — the same
/// id/marker/digest combination `synthesize_native_panic_freedom_to_verifier_api_obligations`
/// mints, recomputed here from `func` like the matcher recomputes it.
fn pf_catchall_obligation_for(
    func: &trust_types::VerifiableFunction,
) -> trust_verifier_api::TrustObligation {
    let source_digest = compiler_function_source_digest_hex(func).expect("source digest");
    let vc_digest = default_trust_mc_function_obligation_digest(
        func,
        &format!("panic-freedom:{}", func.def_path),
    )
    .expect("vc digest");
    trust_verifier_api::TrustObligation {
        obligation_id: format!(
            "vc:{}:assertion:panic-freedom:0",
            trust_types::canonical_artifact_id_component(&func.def_path)
        ),
        kind: trust_verifier_api::ObligationKind::Assertion,
        contract_id: None,
        proof_item_id: None,
        source: source_location_from_trust_span(&func.span),
        description: "panic freedom: no assertion, `unreachable!`, or panic is reachable"
            .to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_verifier_api::MetadataEntry {
                key: TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY.to_string(),
                value: "enabled".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: "trust.vc.kind".to_string(),
                value: "panic_freedom".to_string(),
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: source_digest,
            },
            trust_verifier_api::MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: vc_digest,
            },
        ],
    }
}

#[test]
fn under_precondition_registers_with_open_postcondition() {
    // A `#[requires(P)]` fn: panic site proved-unconditional, the entry
    // assumption for P, the pf catch-all discharged via the DISTINCT
    // under-precondition tag, and an open functional postcondition. Registers
    // UNDER P.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let requires = vc_of_kind(VcKind::Precondition { callee: "self".to_string() });
    let catchall = pf_catchall();
    let post = vc_of_kind(VcKind::Postcondition);
    let auth0 = unconditional_authority(0, &div);
    let results = vec![
        (div, proved()),
        (requires, proved_with_solver(TRUST_ENTRY_ASSUMPTION_SOLVER)),
        (catchall, proved_with_solver("trust-assert-refute-under-precondition")),
        (post, unknown()),
    ];
    let authorities = vec![Some(auth0), None, None, None];
    assert!(
        results_establish_panic_freedom_under_precondition(
            &test_func(),
            true,
            &results,
            &[],
            &authorities
        ),
        "a #[requires(P)] fn with proved panic sites + under-precondition pf discharge \
         must register under P even with an open postcondition"
    );
}

#[test]
fn under_precondition_rejects_unproved_panic_site() {
    // Adversarial (b): a genuinely-panicking callee (its division-by-zero
    // panic site is UNKNOWN) must NOT enter the under-precondition registry.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let requires = vc_of_kind(VcKind::Precondition { callee: "self".to_string() });
    let catchall = pf_catchall();
    let results = vec![
        (div, unknown()),
        (requires, proved_with_solver(TRUST_ENTRY_ASSUMPTION_SOLVER)),
        (catchall, proved_with_solver("trust-assert-refute-under-precondition")),
    ];
    let authorities = vec![None, None, None];
    assert!(
        !results_establish_panic_freedom_under_precondition(
            &test_func(),
            true,
            &results,
            &[],
            &authorities
        ),
        "an unproved panic site must keep a #[requires] fn OUT of the \
         under-precondition registry"
    );
}

#[test]
fn under_precondition_requires_the_distinct_discharge_tag() {
    // Without the DISTINCT under-precondition discharge tag on the catch-all
    // (e.g. it is still Unknown, or was discharged with the UNCONDITIONAL
    // tag), the fn must NOT register under precondition.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let requires = vc_of_kind(VcKind::Precondition { callee: "self".to_string() });
    let catchall = pf_catchall();
    let auth0 = unconditional_authority(0, &div);
    // Catch-all discharged with the UNCONDITIONAL tag — the under-precondition
    // registry must not claim it (it belongs to the unconditional path).
    let results = vec![
        (div, proved()),
        (requires, proved_with_solver(TRUST_ENTRY_ASSUMPTION_SOLVER)),
        (catchall, proved_with_solver("trust-assert-refute")),
    ];
    let authorities = vec![Some(auth0), None, None];
    assert!(
        !results_establish_panic_freedom_under_precondition(
            &test_func(),
            true,
            &results,
            &[],
            &authorities
        ),
        "the under-precondition registry requires the distinct discharge tag"
    );
}

#[test]
fn under_precondition_rejects_non_requires_fn() {
    // A fn with NO #[requires] is handled by the UNCONDITIONAL registry; the
    // conditional registry must never claim it.
    let div = vc_of_kind(VcKind::DivisionByZero);
    let catchall = pf_catchall();
    let auth0 = unconditional_authority(0, &div);
    let results = vec![
        (div, proved()),
        (catchall, proved_with_solver("trust-assert-refute-under-precondition")),
    ];
    let authorities = vec![Some(auth0), None];
    assert!(
        !results_establish_panic_freedom_under_precondition(
            &test_func(),
            false,
            &results,
            &[],
            &authorities
        ),
        "a fn with no #[requires] must not enter the under-precondition registry"
    );
}

#[test]
fn under_precondition_rejects_assume_total_conditionality() {
    // An `assume_total` callee assumption is a DIFFERENT, non-registerable
    // form of conditionality and must fail closed.
    let requires = vc_of_kind(VcKind::Precondition { callee: "self".to_string() });
    let assumed = vc_of_kind(VcKind::Assertion { message: "assumed total".to_string() });
    let catchall = pf_catchall();
    let results = vec![
        (requires, proved_with_solver(TRUST_ENTRY_ASSUMPTION_SOLVER)),
        (assumed, proved_with_solver(TRUST_ASSUMED_TOTAL_SOLVER)),
        (catchall, proved_with_solver("trust-assert-refute-under-precondition")),
    ];
    let authorities = vec![None, None, None];
    assert!(
        !results_establish_panic_freedom_under_precondition(
            &test_func(),
            true,
            &results,
            &[],
            &authorities
        ),
        "an assume_total assumption must keep a fn out of the under-precondition registry"
    );
}

// ---- N1: declared-requires discriminator locks ----

#[test]
fn declared_requires_discriminator_ignores_non_requires_contracts() {
    use trust_types::ContractKind;
    assert!(!has_declared_requires_contract(&[]));
    assert!(!has_declared_requires_contract(&[contract(ContractKind::Ensures)]));
    assert!(has_declared_requires_contract(&[contract(ContractKind::Requires)]));
    assert!(has_declared_requires_contract(&[
        contract(ContractKind::Ensures),
        contract(ContractKind::Requires)
    ]));
}

#[test]
fn synthetic_only_preconditions_fn_registers_unconditionally() {
    // N1 lock: a fn with an i32 param and NO `#[requires]` carries SYNTHETIC
    // type-range entries in `func.preconditions` but an EMPTY declared
    // contract list. It must (a) never enter the under-precondition path —
    // the discriminator, not `preconditions.is_empty()`, decides — and
    // (b) still register UNCONDITIONALLY exactly as before Part B.
    let contracts: Vec<trust_types::Contract> = vec![contract(trust_types::ContractKind::Ensures)];
    assert!(!has_declared_requires_contract(&contracts));

    // (a) even a (mis-)tagged under-precondition discharge cannot register it
    // conditionally once the discriminator says "no declared requires".
    let div = vc_of_kind(VcKind::DivisionByZero);
    let catchall = pf_catchall();
    let auth0 = unconditional_authority(0, &div);
    let results = vec![
        (div, proved()),
        (catchall, proved_with_solver("trust-assert-refute-under-precondition")),
    ];
    let authorities = vec![Some(auth0), None];
    assert!(
        !results_establish_panic_freedom_under_precondition(
            &test_func(),
            has_declared_requires_contract(&contracts),
            &results,
            &[],
            &authorities
        ),
        "synthetic-only preconditions must never route a fn into the conditional registry"
    );

    // (b) the same fn's rows with the UNCONDITIONAL tag + sealed authority
    // register unconditionally (its unknown functional postcondition and its
    // synthetic type-range facts notwithstanding).
    let div = vc_of_kind(VcKind::DivisionByZero);
    let catchall = pf_catchall();
    let post = vc_of_kind(VcKind::Postcondition);
    let auth0 = unconditional_authority(0, &div);
    let auth1 = unconditional_authority(1, &catchall);
    let results = vec![(div, proved()), (catchall, proved()), (post, unknown())];
    let authorities = vec![Some(auth0), Some(auth1), None];
    assert!(
        results_establish_unconditional_panic_freedom(&results, &[], &authorities),
        "a no-declared-requires fn with proved panic sites + catch-all must register \
         unconditionally"
    );
}

// ---- Full-lane pf-restatement identity locks ----

#[test]
fn pf_catchall_identity_accepts_only_the_synthesized_obligation() {
    let func = test_func();
    let obligation = pf_catchall_obligation_for(&func);
    assert!(
        api_obligation_is_panic_freedom_catchall_for(&func, &obligation),
        "the exact synthesized pf catch-all (recomputed id + marker + digests) must match"
    );
}

#[test]
fn pf_catchall_identity_rejects_non_pf_obligations() {
    let func = test_func();

    // Adversarial: a restatement of ANY OTHER obligation kind must not match.
    let mut wrong_kind = pf_catchall_obligation_for(&func);
    wrong_kind.kind = trust_verifier_api::ObligationKind::Postcondition;
    assert!(!api_obligation_is_panic_freedom_catchall_for(&func, &wrong_kind));

    // A different obligation id (e.g. a postcondition's) must not match.
    let mut wrong_id = pf_catchall_obligation_for(&func);
    wrong_id.obligation_id = format!(
        "obligation:{}:postcondition:0",
        trust_types::canonical_artifact_id_component(&func.def_path)
    );
    assert!(!api_obligation_is_panic_freedom_catchall_for(&func, &wrong_id));

    // Missing the panic-freedom marker must not match (a bare Assertion-family
    // obligation — a user assert's own row — carries no such marker).
    let mut no_marker = pf_catchall_obligation_for(&func);
    no_marker.metadata.retain(|entry| entry.key != TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY);
    assert!(!api_obligation_is_panic_freedom_catchall_for(&func, &no_marker));

    // A DUPLICATED marker (ambiguous forgery surface) must not match.
    let mut dup_marker = pf_catchall_obligation_for(&func);
    dup_marker.metadata.push(trust_verifier_api::MetadataEntry {
        key: TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY.to_string(),
        value: "enabled".to_string(),
    });
    assert!(!api_obligation_is_panic_freedom_catchall_for(&func, &dup_marker));

    // An obligation-digest mismatch (obligation minted for a different
    // function identity) must not match — the digest is recomputed from the
    // live func's def-path + span + pf payload.
    let mut wrong_digest = pf_catchall_obligation_for(&func);
    for entry in &mut wrong_digest.metadata {
        if entry.key == TRUST_VC_DIGEST_METADATA_KEY {
            entry.value = format!("{}0", entry.value);
        }
    }
    assert!(!api_obligation_is_panic_freedom_catchall_for(&func, &wrong_digest));

    // The same holds when the FUNCTION IDENTITY differs: another fn's
    // recomputed id + digest can never claim this obligation.
    let mut other_func = test_func();
    other_func.def_path = "test::other".to_string();
    assert!(!api_obligation_is_panic_freedom_catchall_for(
        &other_func,
        &pf_catchall_obligation_for(&func)
    ));
}

#[test]
fn pf_restatement_row_requires_binding_and_restatement_shape() {
    // Without a sealed binding the restatement matcher must never fire —
    // display strings alone (kind/detail) are not identity.
    let func = test_func();
    let vc = vc_of_kind(VcKind::UnsupportedMir {
        kind: "FullVerification::Assertion".to_string(),
        detail: "panic freedom: no assertion, `unreachable!`, or panic is reachable".to_string(),
    });
    assert!(!is_full_lane_panic_freedom_restatement_row(&func, 0, &vc, None));
}
