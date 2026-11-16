//! Original-input selection tests. Closed CIC replay is qualified by Clean's
//! production API suite; these checks cover the independent native adapter.

use clean_olean::semr_native_execution::{
    NativeExecutionContractFormat, NativeExecutionPlace, NativeExecutionType,
};
use trust_ir::{NativeRequestId, ProofId, ValidatedNativeBundle};
use trust_ir_build::validate_module_report;

use super::*;

fn wp_id(native: &NativeVerificationBundle) -> NativeRequestId {
    native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request.id),
            _ => None,
        })
        .unwrap()
}

#[test]
fn complete_original_module_clause_and_binding_order_are_retained() {
    let (public, native) = fixture(false);
    let original = native.clone();
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    assert!(semantics.is_ok(), "{:?}", semantics.errors());
    let subject = native_wp_execution_subject(
        &admitted,
        &semantics,
        wp_id(&native),
        ProofId::new(0),
        &public,
        &public.obligations[0],
    )
    .unwrap();
    let formula = native.module.proof_obligations[0].formula.as_ref().unwrap();
    assert_eq!(subject.module.bytes(), trust_ir::binary::serialize_module(&native.module).unwrap());
    let mut stripped = native.module.clone();
    stripped.proof_obligations.clear();
    assert_ne!(subject.module.bytes(), trust_ir::binary::serialize_module(&stripped).unwrap());
    assert_eq!(&*subject.contract_bytes, formula.payload.as_bytes());
    assert_eq!(subject.contract_format, NativeExecutionContractFormat::BooleanText);
    assert_eq!(subject.function, 0);
    assert_eq!(subject.typed_bindings.len(), 2);
    assert_eq!(subject.typed_bindings[0].name, b"x");
    assert_eq!(subject.typed_bindings[0].place, NativeExecutionPlace::Param(0));
    assert_eq!(subject.typed_bindings[0].ty, NativeExecutionType::Bool);
    assert_eq!(subject.typed_bindings[1].name, b"r");
    assert_eq!(subject.typed_bindings[1].place, NativeExecutionPlace::Result(0));
    assert_eq!(native, original, "selection must not rewrite any original input");
    assert!(public.obligations[0].metadata.iter().any(|row| row.value == "trust-mc"));
}

#[test]
fn a_foreign_semantic_report_cannot_qualify_an_identical_clone() {
    let (public, native) = fixture(false);
    let clone = native.clone();
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let foreign = validate_module_report(&clone.module);
    assert!(foreign.is_ok());
    let error = native_wp_execution_subject(
        &admitted,
        &foreign,
        wp_id(&native),
        ProofId::new(0),
        &public,
        &public.obligations[0],
    )
    .unwrap_err();
    assert!(error.contains("same module"), "{error}");
}

#[test]
fn a_caller_owned_runtime_registry_cannot_qualify_the_input() {
    let (public, native) = fixture(false);
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let registry = trust_ir_build::HandleRegistry::from_pins(&[]).unwrap();
    let config = trust_ir_build::ValidationConfig::pinned().with_handle_registry(&registry);
    let semantics = trust_ir_build::validate_module_with_config(&native.module, &config);
    assert!(semantics.is_ok(), "{:?}", semantics.errors());
    assert!(!semantics.handle_registry_is_pinned());
    let error = native_wp_execution_subject(
        &admitted,
        &semantics,
        wp_id(&native),
        ProofId::new(0),
        &public,
        &public.obligations[0],
    )
    .unwrap_err();
    assert!(error.contains("pinned semantic policy"), "{error}");
}

#[test]
fn wrong_engine_missing_request_and_nonmember_proof_are_refused() {
    let (public, native) = fixture(false);
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    let non_wp = native
        .requests
        .iter()
        .find(|request| !matches!(request, NativeVerificationRequest::TrustWp(_)))
        .unwrap()
        .id();
    for (request, proof) in [
        (non_wp, ProofId::new(0)),
        (NativeRequestId::new(u32::MAX), ProofId::new(0)),
        (wp_id(&native), ProofId::new(u32::MAX)),
    ] {
        assert!(
            native_wp_execution_subject(
                &admitted,
                &semantics,
                request,
                proof,
                &public,
                &public.obligations[0],
            )
            .is_err()
        );
    }
}

#[test]
fn changed_public_contract_or_program_carrier_cannot_select_the_old_input() {
    let (public, native) = fixture(false);
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    let mut changed = public.clone();
    let ContractPredicate::CanonicalJson { value, .. } = &mut changed.contracts[0].predicate else {
        panic!("original exact text contract");
    };
    *value = serde_json::Value::String("false".into());
    assert!(
        native_wp_execution_subject(
            &admitted,
            &semantics,
            wp_id(&native),
            ProofId::new(0),
            &changed,
            &changed.obligations[0],
        )
        .is_err()
    );
    let mut obligation = public.obligations[0].clone();
    obligation.metadata.push(MetadataEntry {
        key: "trust.trust_ir.native.trust_ir_module_digest".into(),
        value: "0".repeat(64),
    });
    assert!(
        native_wp_execution_subject(
            &admitted,
            &semantics,
            wp_id(&native),
            ProofId::new(0),
            &public,
            &obligation,
        )
        .is_err()
    );
}
