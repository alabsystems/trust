//! Native-request metadata admission controls; synthetic claims are not proofs.

use trust_ir::{
    CertificateBinding, CleanCicKernelRecheck, ModuleCompleteness, ModuleImport, ProofEvidence,
    SpecModule, SpecVar, UnloweredRow,
};

use super::tests::native_request_module_without_trust_vc_lane;
use super::*;

fn digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

pub(crate) fn add_wire_v46_content(module: &mut Module) {
    let mut spec = SpecModule::design_only("non_certifying_wire_control");
    spec.vars.push(SpecVar::new("ready", "Bool").with_sort(trust_ir::proof::ClauseSort::Bool));
    module.spec_modules.push(spec);
    assert_eq!(
        ProjectedModuleBinaryPlan::try_new(module, ModuleBinaryOptions::default()).err(),
        Some(BinaryProjectionError::SpecCarrierRequiresV46),
        "the control must distinguish adaptive Raw from the v38 default"
    );
}

/// Include valid and invalid claims: none is encodable, regardless of semantic
/// validation. Certificate bytes and bindings are deliberately not proof input.
pub(crate) fn nonwire_cases(plain: &Module) -> Vec<(Module, BinaryProjectionError)> {
    let row = UnloweredRow {
        symbol: "not_lowered".into(),
        display_path: Some("source::not_lowered".into()),
        reason: "synthetic admission control".into(),
    };
    let mut cases = Vec::new();
    for claim in [
        ModuleCompleteness::Complete,
        ModuleCompleteness::Partial(vec![]),
        ModuleCompleteness::Partial(vec![row.clone()]),
        ModuleCompleteness::Partial(vec![row.clone(), row.clone()]),
        ModuleCompleteness::Partial(vec![UnloweredRow {
            symbol: plain.functions[0].name.clone(),
            ..row
        }]),
    ] {
        let mut module = plain.clone();
        module.completeness = Some(claim);
        cases.push((module, BinaryProjectionError::CompletenessClaimUnencodable));
    }
    let mut bound = plain.clone();
    let obligation = ProofId::new(73);
    // trust-ir v61 gave `CertificateBinding` a binary carrier, so a bound
    // certificate is no longer a non-wire claim of its own (the
    // `CertificateBindingUnencodable` refusal is gone). The bound rows ride
    // along into the two refusals below, which they must not change.
    bound.proof_certificates.push(ProofCertificate {
        obligation,
        prover: "synthetic unbound transport control".into(),
        evidence: ProofEvidence::LeanProof("not a proof".into()),
        assurance: None,
    });
    bound.proof_certificates.push(ProofCertificate {
        obligation,
        prover: "synthetic bound transport control".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage: digest(1),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "TransportFixture".into(),
                theorems: vec![],
                anchor: "transport-fixture".into(),
                allowed_axioms: vec![],
                binding: Some(Box::new(CertificateBinding::new(digest(2), digest(3)))),
            }),
        },
        assurance: None,
    });
    bound.completeness = Some(ModuleCompleteness::Complete);
    cases.push((bound.clone(), BinaryProjectionError::CompletenessClaimUnencodable));
    // The shared upstream preflight also retains the existing lexical-scope
    // refusal and its precedence over the completeness claim.
    bound.functions[0].scopes = Some(vec![trust_ir::ScopeData {
        parent: None,
        span: None,
        inlined_at: Some(trust_ir::InlinedAt {
            span: SourceSpan { file: 0, line: 1, col: 1 },
            callee: "synthetic::callee".into(),
        }),
    }]);
    let function = bound.functions[0].id.index();
    cases.push((bound, BinaryProjectionError::InlinedScopeChainUnencodable { function, scope: 0 }));
    cases
}

pub(crate) fn assert_binary_admission_refusal(module: &Module, expected: &BinaryProjectionError) {
    let before = module.clone();
    assert_eq!(require_native_module_binary_identity(module), Err(expected.clone()));
    assert_eq!(*module, before, "admission must preserve claims and diagnostic input");
    let upstream = ProjectedModuleBinaryPlan::try_new(
        module,
        ModuleBinaryOptions {
            body: ModuleBinaryBody::Raw,
            symbols: ModuleSymbolProjection::Exact,
            obligations: ModuleObligationRows::All,
        },
    )
    .err()
    .expect("upstream refuses the exact original module");
    assert_eq!(upstream, *expected);
}

#[test]
fn native_metadata_none_preserves_canonical_digest_and_actual_producer_tags() {
    for v46 in [false, true] {
        let mut module = native_request_module_without_trust_vc_lane();
        if v46 {
            add_wire_v46_content(&mut module);
        }
        assert_eq!(module.completeness, None);
        let canonical_digest = module.stable_digest();
        let bundle =
            native_verification_bundle_from_module(module.clone(), digest(4), FuncId::new(0))
                .expect("claim-free MIR module retains its canonical identity");
        assert_eq!(bundle.module, module);
        assert_eq!(bundle.trust_ir_module_digest, canonical_digest);
        assert_eq!(bundle.provenance.source_language, NativeSourceLanguage::Rust);
        assert_eq!(
            bundle.provenance.source_languages,
            BTreeSet::from([NativeSourceLanguage::Rust, NativeSourceLanguage::TrustIr])
        );
        assert!(
            bundle
                .module
                .functions
                .iter()
                .all(|function| { function.producer == Some(Producer::TrustIr) })
        );
    }
}

#[test]
fn native_metadata_primary_and_function_language_omissions_fail() {
    let bundle = native_verification_bundle_from_module(
        native_request_module_without_trust_vc_lane(),
        digest(4),
        FuncId::new(0),
    )
    .unwrap();
    for omitted in [NativeSourceLanguage::Rust, NativeSourceLanguage::TrustIr] {
        let mut altered = bundle.clone();
        altered.provenance.source_languages.remove(&omitted);
        let errors = altered.validate().expect_err("omission is not a wildcard");
        assert!(
            errors.iter().any(|error| match omitted {
                NativeSourceLanguage::Rust => matches!(error,
                NativeVerificationBundleError::BundlePrimaryLanguageUncovered { primary, .. }
                    if *primary == NativeSourceLanguage::Rust),
                NativeSourceLanguage::TrustIr => matches!(error,
                NativeVerificationBundleError::BundleLanguageUncovered { producer, .. }
                    if *producer == Some(Producer::TrustIr)),
                _ => unreachable!(),
            }),
            "{errors:?}"
        );
    }
}

#[test]
fn native_metadata_does_not_infer_foreign_or_unknown_import_languages() {
    for producer in [
        None,
        Some(Producer::Clean),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("foreign".into())),
    ] {
        let mut module = native_request_module_without_trust_vc_lane();
        let mut import = ModuleImport::new("unadmitted_dependency", digest(5));
        import.producer = producer.clone();
        module.imports.push(import);
        let error = native_verification_bundle_from_module(module, digest(4), FuncId::new(0))
            .expect_err("imports cannot broaden this planner's admitted language set");
        let NativeVerificationBundleBuildError::Validation(errors) = error else {
            panic!("expected upstream import diagnostic, got {error:?}")
        };
        assert!(
            errors.iter().any(|error| matches!(error,
                NativeVerificationBundleError::BundleImportLanguageUncovered {
                    producer: actual, name, ..
                } if *actual == producer && name == "unadmitted_dependency"
            )),
            "{errors:?}"
        );
    }
}

#[test]
fn native_metadata_refuses_nonwire_claims_before_digest_without_erasure() {
    let plain = native_request_module_without_trust_vc_lane();
    for (module, expected) in nonwire_cases(&plain) {
        assert_binary_admission_refusal(&module, &expected);
        let before = module.clone();
        let error =
            native_verification_bundle_from_module(module.clone(), digest(4), FuncId::new(0))
                .expect_err("every non-wire carrier must refuse before the digest can panic");
        assert_eq!(
            error,
            NativeVerificationBundleBuildError::ModuleBinaryIdentity(expected.clone())
        );
        assert!(error.to_string().ends_with(&expected.to_string()));
        assert_eq!(module, before);
    }
}
