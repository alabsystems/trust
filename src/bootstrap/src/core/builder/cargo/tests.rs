use super::{
    Rustflags, TRUST_BOOTSTRAP_NO_VERIFY_FLAG, apply_bootstrap_trust_verification_default,
    bootstrap_disables_default_trust_verification, effective_codegen_units,
    effective_debuginfo_level, flags_env, rustflags_contain_trust_verifier_control,
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

/// Reproduce `Cargo::from`'s composition: bootstrap's own flags, then the
/// verification default, then the env pair Cargo is handed.
fn bootstrap_rustflags_env(
    build_compiler_stage: u32,
    bootstrap_flags: &[&str],
) -> (String, String) {
    let mut rustflags = Rustflags::new(TargetSelection::from_user("aarch64-apple-darwin"));
    for flag in bootstrap_flags {
        rustflags.arg(flag);
    }
    apply_bootstrap_trust_verification_default(&mut rustflags, build_compiler_stage);
    let (var, value) = flags_env("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", &rustflags.0);
    (var.to_string(), value)
}

/// The regression this pins: Cargo honours exactly ONE rustflags source, so the
/// off-switch has to be in the same payload as bootstrap's other flags. Deliver
/// it through `CARGO_TARGET_<TRIPLE>_RUSTFLAGS` instead and Cargo drops it on
/// the floor, silently verifying the whole third-party dependency graph.
#[test]
fn bootstrap_off_switch_rides_the_same_lane_as_bootstrap_s_other_flags() {
    // `-Wrust_2018_idioms` is unconditional in bootstrap, so the competing
    // `RUSTFLAGS`/`CARGO_ENCODED_RUSTFLAGS` lane always exists in practice.
    let (var, value) = bootstrap_rustflags_env(1, &["-Wrust_2018_idioms", "-Wunused_lifetimes"]);

    assert!(matches!(var.as_str(), "RUSTFLAGS" | "CARGO_ENCODED_RUSTFLAGS"), "{var}");
    assert!(value.contains(TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{var}={value:?}");
    assert!(value.contains("-Wrust_2018_idioms"), "{var}={value:?}");
}

#[test]
fn bootstrap_off_switch_survives_when_bootstrap_has_no_other_flags() {
    let (var, value) = bootstrap_rustflags_env(1, &[]);

    assert_eq!(var, "RUSTFLAGS");
    assert_eq!(value, TRUST_BOOTSTRAP_NO_VERIFY_FLAG);
}

#[test]
fn stage0_units_keep_the_seed_default() {
    let (_, value) = bootstrap_rustflags_env(0, &["-Wrust_2018_idioms"]);

    assert!(!value.contains("trust-verify"), "{value:?}");
}

#[test]
fn an_explicit_off_switch_is_not_duplicated() {
    let (_, value) = bootstrap_rustflags_env(1, &["-Ztrust-verify=off"]);

    assert_eq!(value.matches(TRUST_BOOTSTRAP_NO_VERIFY_FLAG).count(), 1, "{value:?}");
}

/// A deliberate developer control keeps ownership of the verifier surface: the
/// default must not append a second, later-winning `-Z` on top of it.
#[test]
fn a_deliberate_verifier_control_suppresses_the_default() {
    let mut rustflags = Rustflags::new(TargetSelection::from_user("aarch64-apple-darwin"));
    rustflags.arg("-Ztrust-verify-output=json");
    apply_bootstrap_trust_verification_default(&mut rustflags, 1);

    assert!(!rustflags.0.contains(TRUST_BOOTSTRAP_NO_VERIFY_FLAG), "{:?}", rustflags.0);
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
