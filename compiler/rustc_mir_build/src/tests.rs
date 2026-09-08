#[test]
fn direct_thir_lowering_never_grants_implicit_proof_authority() {
    // Trust (Step 2/3, owner directive 2026-08-30): marker moved to the
    // obligation-bearing-pending tier. The two authority asserts are the
    // point of this pin and did NOT move.
    let capability = trust_thir_lower::crate_module::DIRECT_OBLIGATION_CAPABILITY;
    assert_eq!(capability.marker(), "obligation-bearing-pending-v2");
    assert!(!capability.grants_proof_authority());
    assert!(!capability.emits_native_verification_requests());
}
