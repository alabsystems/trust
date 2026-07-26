#[test]
fn direct_thir_lowering_never_grants_implicit_proof_authority() {
    let capability = trust_thir_lower::crate_module::DIRECT_OBLIGATION_CAPABILITY;
    assert_eq!(capability.marker(), "structural-parity-only-v1");
    assert!(!capability.grants_proof_authority());
    assert!(!capability.emits_native_verification_requests());
}
