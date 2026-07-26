use super::{
    bootstrap_disables_default_trust_verification, cargo_target_rustflags_env,
    effective_codegen_units, effective_debuginfo_level, rustflags_contain_trust_verifier_control,
    rustflags_request_bootstrap_verification, trust_cg_codegen_flags, trust_cg_codegen_is_active,
};
use crate::core::config::DebuginfoLevel;
use crate::{CodegenBackendKind, TargetSelection};

#[test]
fn trust_verifier_control_detection_accepts_combined_and_split_flags() {
    assert!(rustflags_contain_trust_verifier_control("-Ztrust-verify-full"));
    assert!(rustflags_contain_trust_verifier_control("-Ztrust-verify=on"));
    assert!(rustflags_contain_trust_verifier_control("-Ztrust-policy=advisory"));
    assert!(rustflags_contain_trust_verifier_control("-Z trust-verify-output=json"));
    assert!(rustflags_contain_trust_verifier_control("-Ztrust-verify-function-budget-ms=60000"));
    assert!(rustflags_contain_trust_verifier_control("-Ztrust-policy=memory-safe"));
    assert!(!rustflags_contain_trust_verifier_control("-Zrandomize-layout -Cdebuginfo=2"));
    assert!(!rustflags_contain_trust_verifier_control("-Ztrustworthy-layout"));
}

#[test]
fn non_stage0_bootstrap_uses_no_verify_env_by_default() {
    assert!(bootstrap_disables_default_trust_verification(1, ""));
}

#[test]
fn stage0_bootstrap_does_not_use_no_verify_env() {
    assert!(!bootstrap_disables_default_trust_verification(0, ""));
}

#[test]
fn explicit_trust_verifier_controls_suppress_bootstrap_default_env() {
    assert!(!bootstrap_disables_default_trust_verification(1, "-Z trust-verify-output=json"));
}

#[test]
fn bootstrap_allows_only_the_exact_off_switch() {
    assert!(!rustflags_request_bootstrap_verification("-Ztrust-verify=off"));
    assert!(!rustflags_request_bootstrap_verification("-Z trust-verify=off"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify=on"));
    assert!(rustflags_request_bootstrap_verification("-Ztrust-verify-full"));
    assert!(rustflags_request_bootstrap_verification("-Z trust-policy=advisory"));
}

#[test]
fn bootstrap_no_verify_uses_target_specific_rustflags_env() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");

    assert_eq!(cargo_target_rustflags_env(target), "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS");
}

#[test]
fn trust_cg_abort_policy_starts_with_the_staged_compiler() {
    assert!(!trust_cg_codegen_is_active(0, &CodegenBackendKind::TrustCg));
    assert!(trust_cg_codegen_is_active(1, &CodegenBackendKind::TrustCg));
    assert!(trust_cg_codegen_is_active(2, &CodegenBackendKind::TrustCg));
    assert!(!trust_cg_codegen_is_active(1, &CodegenBackendKind::Llvm));
    assert!(!trust_cg_codegen_is_active(1, &CodegenBackendKind::Custom("other".into())));
}

#[test]
fn trust_cg_profiles_disable_unimplemented_debuginfo() {
    assert_eq!(effective_debuginfo_level(true, DebuginfoLevel::Full), DebuginfoLevel::None);
    assert_eq!(
        effective_debuginfo_level(true, DebuginfoLevel::LineTablesOnly),
        DebuginfoLevel::None
    );
    assert_eq!(
        effective_debuginfo_level(false, DebuginfoLevel::LineTablesOnly),
        DebuginfoLevel::LineTablesOnly
    );
}

#[test]
fn trust_cg_profiles_force_the_single_supported_codegen_unit() {
    assert_eq!(effective_codegen_units(true, None), Some(1));
    assert_eq!(effective_codegen_units(true, Some(16)), Some(1));
    assert_eq!(effective_codegen_units(false, Some(16)), Some(16));
    assert_eq!(effective_codegen_units(false, None), None);
}

#[test]
fn trust_cg_panic_flags_cover_normal_and_test_units() {
    assert_eq!(trust_cg_codegen_flags(false, false), &[] as &[&str]);
    assert_eq!(trust_cg_codegen_flags(false, true), &[] as &[&str]);
    assert_eq!(trust_cg_codegen_flags(true, false), &["-Cpanic=abort"]);
    assert_eq!(trust_cg_codegen_flags(true, true), &["-Cpanic=abort", "-Zpanic-abort-tests"]);
}
