//! Typed identity controls. Actual compiler-origin fixtures are qualified by
//! the compiler callback regression; these unit fixtures assert binding only.
use trust_types::expanded_function_identity::*;
use trust_types::*;

#[derive(serde::Deserialize)]
struct Certificate {
    source: Source,
}
#[derive(serde::Deserialize)]
struct Source {
    function: VerifiableFunction,
    compiler_contracts: CompilerContractBundle,
    source_vc: VerificationCondition,
    target: String,
    overflow_checks: bool,
}
fn fixture() -> (Source, ExpandedFunctionIdentity) {
    let source: Source = trust_types::json_depth::from_str_deep::<Certificate>(include_str!(
        "fixtures/source_clause_certificate.json"
    ))
    .unwrap()
    .source;
    let span = SourceSpan {
        file: "fixture.rs".into(),
        line_start: 1,
        col_start: 0,
        line_end: 1,
        col_end: 50,
    };
    let identity = ExpandedFunctionIdentity {
        schema: EXPANDED_FUNCTION_IDENTITY_SCHEMA.into(),
        function_path: source.function.def_path.clone(),
        function_def_path_hash: [7, 1],
        macro_path: "source_clause_fixture::make_fn".into(),
        macro_def_path_hash: [7, 2],
        definition: ExpansionSourceFragment::from_exact_snippet(
            span.clone(),
            "macro_rules! make_fn { () => { fn constant_false() -> bool { false } } }",
        )
        .unwrap(),
        invocation: ExpansionSourceFragment::from_exact_snippet(span, "make_fn!();").unwrap(),
        typed_input_sha256: expanded_typed_input_digest(
            &source.function,
            &source.compiler_contracts,
        )
        .unwrap(),
    };
    (source, identity)
}
#[test]
fn expanded_identity_binds_each_input_and_rejects_malformed_provenance() {
    let (source, identity) = fixture();
    assert!(identity.matches_input(&source.function, &source.compiler_contracts));
    for i in 0..7 {
        let mut changed = identity.clone();
        match i {
            0 => changed.definition.sha256 = "1".repeat(64),
            1 => changed.invocation.sha256 = "2".repeat(64),
            2 => changed.typed_input_sha256 = "3".repeat(64),
            3 => changed.function_def_path_hash[1] += 1,
            4 => changed.macro_def_path_hash[1] += 1,
            5 => changed.definition.span.col_end += 1,
            _ => changed.function_path.push('x'),
        }
        assert_ne!(changed.digest(), identity.digest(), "mutation {i}");
    }
    for i in 0..6 {
        let mut bad = identity.clone();
        match i {
            0 => bad.schema.push('x'),
            1 => bad.macro_def_path_hash[0] += 1,
            2 => bad.definition.byte_len = 0,
            3 => bad.invocation.byte_len = MAX_EXPANSION_SOURCE_BYTES as u64 + 1,
            4 => bad.typed_input_sha256 = "bad".into(),
            _ => bad.definition.span.line_start = 0,
        }
        assert!(bad.digest().is_none(), "mutation {i}");
    }
}
#[test]
fn expanded_identity_is_distinct_from_ordinary_and_bound_into_outer_claim() {
    let (source, identity) = fixture();
    let typed = "c".repeat(64);
    let vc = &source.source_vc;
    let ordinary = original_vc_snapshot::exact_vc_claim_digest_with_typed_input_sha256(
        vc,
        source.overflow_checks,
        Some(&source.target),
        Some(&typed),
    )
    .unwrap();
    assert_eq!(
        Some(ordinary.clone()),
        original_vc_snapshot::exact_vc_claim_digest_with_expanded_identity(
            vc,
            source.overflow_checks,
            Some(&source.target),
            Some(&typed),
            None
        )
    );
    let digest = original_vc_snapshot::exact_vc_claim_digest_with_expanded_identity(
        vc,
        source.overflow_checks,
        Some(&source.target),
        Some(&typed),
        Some(&identity),
    )
    .unwrap();
    assert_ne!(digest, ordinary);
    let snapshot = OriginalVcSnapshot::capture_with_expanded_identity(
        vc,
        source.overflow_checks,
        &source.target,
        "owner",
        &digest,
        Some(&typed),
        Some(&identity),
    )
    .unwrap();
    assert!(snapshot.decode_for_row("owner", &digest).is_ok());
    let mut bad = snapshot.clone();
    bad.expanded_function_identity = None;
    assert!(bad.decode_for_row("owner", &digest).is_err());
    let mut bad = snapshot.clone();
    bad.expanded_function_identity.as_mut().unwrap().invocation.sha256 = "d".repeat(64);
    assert!(bad.decode_for_row("owner", &digest).is_err());
    assert!(
        OriginalVcSnapshot::capture_with_expanded_identity(
            vc,
            source.overflow_checks,
            &source.target,
            "owner",
            &ordinary,
            Some(&typed),
            Some(&identity)
        )
        .is_none()
    );
    assert!(
        original_vc_snapshot::exact_vc_claim_digest_with_expanded_identity(
            vc,
            source.overflow_checks,
            Some(&source.target),
            None,
            Some(&identity)
        )
        .is_none()
    );
}
