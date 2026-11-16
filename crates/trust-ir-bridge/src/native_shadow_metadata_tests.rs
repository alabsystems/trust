//! Direct shadow metadata controls; no source anchor or proof claim is minted.

use trust_ir::ModuleImport;

use super::tests::direct_shadow_module_fixture;
use super::*;
use crate::native_request::metadata_tests::{
    add_wire_v46_content, assert_binary_admission_refusal, nonwire_cases,
};

#[test]
fn shadow_metadata_languages_cover_only_actual_admitted_functions() {
    for clean_join in [false, true] {
        for v46 in [false, true] {
            let mut module = direct_shadow_module_fixture();
            if !clean_join {
                module.functions.retain(|function| function.producer != Some(Producer::Clean));
            }
            if v46 {
                add_wire_v46_content(&mut module);
            }
            let functions = module.functions.clone();
            assert_eq!(module.completeness, None);
            let pristine = module.stable_digest();
            let shadow = direct_shadow_verification_bundle_from_module(module)
                .expect("existing claim-free joins remain admitted");
            let bundle = shadow.bundle();
            let mut expected =
                BTreeSet::from([NativeSourceLanguage::TrustIr, NativeSourceLanguage::Rust]);
            if clean_join {
                expected.insert(NativeSourceLanguage::Clean);
            }
            assert_eq!(bundle.provenance.source_language, NativeSourceLanguage::TrustIr);
            assert_eq!(bundle.provenance.source_languages, expected);
            assert_eq!(bundle.module.functions, functions, "never relabel original producers");
            assert_eq!(bundle.provenance.source_digest, None);
            assert_eq!(bundle.source_digest(), None);
            assert_eq!(shadow.disclosure.pristine_module_digest, pristine);
            assert_eq!(bundle.trust_ir_module_digest, bundle.module.stable_digest());
            assert_eq!(bundle.module.completeness, None);
        }
    }
}

#[test]
fn shadow_metadata_primary_rust_and_clean_omissions_fail() {
    let shadow =
        direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture()).unwrap();
    for omitted in
        [NativeSourceLanguage::TrustIr, NativeSourceLanguage::Rust, NativeSourceLanguage::Clean]
    {
        let mut bundle = shadow.bundle().clone();
        bundle.provenance.source_languages.remove(&omitted);
        let errors = bundle.validate().expect_err("the primary and both producers must be covered");
        assert!(
            errors.iter().any(|error| match omitted {
                NativeSourceLanguage::TrustIr => matches!(error,
                NativeVerificationBundleError::BundlePrimaryLanguageUncovered { primary, .. }
                    if *primary == NativeSourceLanguage::TrustIr),
                NativeSourceLanguage::Rust => matches!(error,
                NativeVerificationBundleError::BundleLanguageUncovered { producer, .. }
                    if *producer == Some(Producer::TRust)),
                NativeSourceLanguage::Clean => matches!(error,
                NativeVerificationBundleError::BundleLanguageUncovered { producer, .. }
                    if *producer == Some(Producer::Clean)),
                _ => unreachable!(),
            }),
            "{errors:?}"
        );
    }
}

#[test]
fn shadow_metadata_imports_do_not_expand_the_admitted_language_set() {
    for producer in [
        None,
        Some(Producer::Clean),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("foreign".into())),
    ] {
        let mut module = direct_shadow_module_fixture();
        // An import alone cannot manufacture a Clean half of the package.
        module.functions.retain(|function| function.producer != Some(Producer::Clean));
        let mut import = ModuleImport::new("unadmitted_dependency", ProofDigest::sha256([5; 32]));
        import.producer = producer.clone();
        module.imports.push(import);
        let error = direct_shadow_verification_bundle_from_module(module)
            .expect_err("do not infer an imported language outside admitted producer rows");
        let DirectShadowBundleBuildError::Validation(errors) = error else {
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
fn shadow_metadata_refuses_nonwire_claims_before_digest_or_enrichment() {
    let plain = direct_shadow_module_fixture();
    for (module, expected) in nonwire_cases(&plain) {
        assert_binary_admission_refusal(&module, &expected);
        let before = module.clone();
        let error = direct_shadow_verification_bundle_from_module(module.clone())
            .expect_err("non-wire metadata must never be dropped or hashed");
        assert_eq!(error, DirectShadowBundleBuildError::ModuleBinaryIdentity(expected.clone()));
        assert!(error.to_string().ends_with(&expected.to_string()));
        assert_eq!(module, before, "original public identities and all claims remain intact");
    }
}
