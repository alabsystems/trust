use super::*;
use std::str::FromStr;

fn flags(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

#[test]
fn complete_project_requirements_are_typed_and_not_activation() {
    let mut policy = ProjectTrustPolicy::default();
    policy
        .require_scope(
            &flags(&[
                "-Ztrust-verify=on",
                "-Ztrust-policy=certify",
                "-Ztrust-verify-level=2",
                "-Ztrust-verify-profile=unix_hardened",
                "-Ztrust-verify-include-dependencies=yes",
                "-Ztrust-ir-lower=strict",
                "-Copt-level=1",
            ]),
            "target",
        )
        .unwrap();
    assert_eq!(policy.policy, Some(Policy::Certify));
    assert_eq!(policy.level, Some(2));
    assert_eq!(policy.include_dependencies, Some(true));
    assert_eq!(policy.ir_lower, Some(IrLower::Strict));
    assert!(policy.verification_required);
    let wire = serde_json::to_value(&policy).unwrap();
    assert_eq!(wire["schema"], "trust.project-policy.v1");
    assert!(wire.get("session").is_none());
}

#[test]
fn host_target_and_rustdoc_requirements_must_agree() {
    let mut policy = ProjectTrustPolicy::default();
    policy
        .require_scope(
            &flags(&[
                "-Ztrust-policy=certify",
                "-Ztrust-verify-include-dependencies=yes",
            ]),
            "target",
        )
        .unwrap();
    policy
        .require_scope(
            &flags(&[
                "-Ztrust-policy=certify",
                "-Ztrust-verify-include-dependencies=true",
            ]),
            "host",
        )
        .unwrap();
    assert!(
        policy
            .require_scope(&flags(&["-Ztrust-policy=advisory"]), "rustdoc")
            .is_err()
    );
    assert!(
        policy
            .require_scope(&flags(&["-Ztrust-verify-include-dependencies=no"]), "host")
            .is_err()
    );
}

#[test]
fn source_session_off_duplicate_and_retired_authority_refuse() {
    for values in [
        vec!["-Ztrust-verify=off"],
        vec!["-Zno-trust-verify=yes"],
        vec!["-Ztrust-verification-session=forged"],
        vec!["-Ztrust-proof-artifact-root=/tmp/proof"],
        vec!["-Ztrust-verify-role=primary"],
        vec!["-Zcontract-checks=off"],
        vec!["-Ztrust-policy=certify", "-Ztrust_policy=certify"],
    ] {
        assert!(
            ProjectTrustPolicy::default()
                .require_scope(&flags(&values), "config")
                .is_err(),
            "{values:?}"
        );
    }
}

#[test]
fn invalid_and_missing_values_do_not_select_defaults() {
    for value in [
        "-Ztrust-policy",
        "-Ztrust-policy=unknown",
        "-Ztrust-verify-level=3",
        "-Ztrust-ir-lower=unknown",
        "-Ztrust-verify-profile=",
    ] {
        assert!(
            ProjectTrustPolicy::default()
                .require_scope(&flags(&[value]), "config")
                .is_err(),
            "{value}"
        );
    }
}

fn context(config: &str, host_config: bool) -> (tempfile::TempDir, GlobalContext) {
    let temp = tempfile::tempdir().unwrap();
    std::fs::create_dir(temp.path().join(".cargo")).unwrap();
    std::fs::write(temp.path().join(".cargo/config.toml"), config).unwrap();
    let mut gctx = GlobalContext::new(
        cargo_util_terminal::Shell::new(),
        temp.path().to_path_buf(),
        temp.path().join("home"),
    );
    gctx.set_search_stop_path(temp.path().to_path_buf());
    gctx.set_env(Default::default());
    gctx.nightly_features_allowed = true;
    let unstable = if host_config {
        flags(&["host-config", "target-applies-to-host"])
    } else {
        Vec::new()
    };
    gctx.configure(0, false, None, false, false, true, &None, &unstable, &[])
        .unwrap();
    (temp, gctx)
}

#[test]
fn cargo_matching_cfg_and_triple_override_build_requirements() {
    let (_temp, gctx) = context(
        r#"
[build]
rustflags = ["-Ztrust-policy=advisory"]
[target.aarch64-unknown-linux-gnu]
rustflags = ["-Ztrust-verify-level=2"]
[target.'cfg(unix)']
rustflags = ["-Ztrust-policy=certify"]
"#,
        false,
    );
    let cfg = vec![Cfg::from_str("unix").unwrap()];
    let resolved = configured_scope(
        &gctx,
        &[CompileKind::Host],
        "aarch64-unknown-linux-gnu",
        &cfg,
        CompileKind::Host,
        Flags::Rust,
    )
    .unwrap();
    let mut policy = ProjectTrustPolicy::default();
    policy.require_scope(&resolved, "target").unwrap();
    assert_eq!(policy.policy, Some(Policy::Certify));
    assert_eq!(policy.level, Some(2));
}

#[test]
fn unmatched_cfg_falls_back_and_ordinary_target_flags_do_not_merge_build() {
    let (_temp, gctx) = context(
        r#"
[build]
rustflags = ["-Ztrust-policy=certify"]
[target.'cfg(windows)']
rustflags = ["-Ztrust-policy=advisory"]
[target.aarch64-unknown-linux-gnu]
rustflags = ["-Copt-level=1"]
"#,
        false,
    );
    let cfg = vec![Cfg::from_str("unix").unwrap()];
    for (host, expected) in [
        ("x86_64-unknown-linux-gnu", Some(Policy::Certify)),
        ("aarch64-unknown-linux-gnu", None),
    ] {
        let resolved = configured_scope(
            &gctx,
            &[CompileKind::Host],
            host,
            &cfg,
            CompileKind::Host,
            Flags::Rust,
        )
        .unwrap();
        let mut policy = ProjectTrustPolicy::default();
        policy.require_scope(&resolved, "target").unwrap();
        assert_eq!(policy.policy, expected);
    }
}

#[test]
fn explicit_target_import_checks_actual_isolated_host_requirements() {
    let (_temp, gctx) = context(
        r#"
[host]
rustflags = ["-Ztrust-policy=advisory"]
[target.aarch64-unknown-linux-gnu]
rustflags = ["-Ztrust-policy=certify"]
"#,
        true,
    );
    let target =
        CompileKind::Target(CompileTarget::new("aarch64-unknown-linux-gnu", false).unwrap());
    let cfg = vec![Cfg::from_str("unix").unwrap()];
    let mut policy = ProjectTrustPolicy::default();
    let host_flags = configured_scope(
        &gctx,
        &[target],
        "aarch64-unknown-linux-gnu",
        &cfg,
        CompileKind::Host,
        Flags::Rust,
    )
    .unwrap();
    policy.require_scope(&host_flags, "host").unwrap();
    let target_flags = configured_scope(
        &gctx,
        &[target],
        "aarch64-unknown-linux-gnu",
        &cfg,
        target,
        Flags::Rust,
    )
    .unwrap();
    assert!(policy.require_scope(&target_flags, "target").is_err());
}

#[test]
fn actual_rustdoc_config_conflict_is_not_dropped() {
    let (_temp, gctx) = context(
        r#"
[build]
rustflags = ["-Ztrust-policy=certify", "-Ztrust-verify-include-dependencies=yes"]
rustdocflags = ["-Ztrust-policy=certify", "-Ztrust-verify-include-dependencies=no"]
"#,
        false,
    );
    let mut policy = ProjectTrustPolicy::default();
    for flags in [Flags::Rust, Flags::Rustdoc] {
        let resolved = configured_scope(
            &gctx,
            &[CompileKind::Host],
            "aarch64-unknown-linux-gnu",
            &[],
            CompileKind::Host,
            flags,
        )
        .unwrap();
        let result = policy.require_scope(&resolved, "config");
        match flags {
            Flags::Rust => assert!(result.is_ok()),
            Flags::Rustdoc => assert!(result.is_err()),
        }
    }
}
