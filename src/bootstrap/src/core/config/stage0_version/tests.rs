use super::*;
fn metadata() -> Stage0 {
    let mut value = Stage0::default();
    value.config.min_stage0_rustc_version = "1.100.0".into();
    value.config.min_stage0_cargo_version = "1.98.0".into();
    value
}
fn check(output: &str, role: &str) -> bool {
    validate(output, role, &metadata(), "1.101.0").is_ok()
}
#[test]
fn genuine_planner_line_does_not_lower_the_compiler_floor() {
    assert!(check("targo 1.98.0 (23032d576 2026-11-08)", "targo"));
    assert!(!check("trustc 1.98.0 (23032d576 2026-11-08)", "trustc"));
    assert!(check("trustc 1.101.0-dev (29ebb403d 2026-10-28)", "trustc"));
    assert!(!check("trustc 1.99.0-dev", "trustc"));
    assert!(check("rustc 1.100.0-beta.7", "trustc"));
}
#[test]
fn both_supported_planner_label_origins_and_upstream_name_are_checked() {
    assert!(check("targo 1.101.0-dev (7fd22bfe8 2026-11-08)", "targo"));
    assert!(check("cargo 1.98.0", "targo"));
    assert!(check("targo 1.99.0", "targo"));
    assert!(!check("trustc 1.99.0", "trustc"));
}
#[test]
fn lower_and_future_tools_still_refuse_by_their_own_role() {
    for line in ["targo 1.97.9", "cargo 1.102.0", "targo 2.0.0", "targo 1.101.0+unqualified"] {
        assert!(!check(line, "targo"));
    }
    for line in ["trustc 1.99.9", "rustc 1.102.0", "rustc 1.101.0+unqualified"] {
        assert!(!check(line, "trustc"));
    }
}
#[test]
fn unknown_wrong_role_missing_and_malformed_observations_refuse() {
    for output in [
        "",
        "targo",
        "targo not-a-version",
        "targo 1.98.0-invalid!",
        " targo 1.98.0",
        "targo  1.98.0",
        "targo\t1.98.0",
        "trustc 1.101.0",
        "cargo 1.98",
    ] {
        assert!(!check(output, "targo"), "{output:?}");
    }
    assert!(!check("targo 1.98.0", "trustc"));
    assert!(!check("tool 1.101.0", "tool"));
}
#[test]
fn missing_or_invalid_planner_policy_never_falls_back_to_compiler_or_zero() {
    for value in ["", "invalid", "1.98.0-dev", "1.102.0"] {
        let mut policy = metadata();
        policy.config.min_stage0_cargo_version = value.into();
        assert!(validate("targo 1.101.0", "targo", &policy, "1.101.0").is_err());
        assert!(validate("trustc 1.101.0", "trustc", &policy, "1.101.0").is_ok());
    }
    assert!(validate("targo 1.98.0", "targo", &metadata(), "unavailable").is_err());
}
